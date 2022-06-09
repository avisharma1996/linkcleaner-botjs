require('dotenv').config();
const Discord = require('discord.js');
var SpotifyWebApi = require('spotify-web-api-node');
var spotifyApi;
require('discord-inline-reply');
const client = new Discord.Client({
  partials: ['MESSAGE', 'CHANNEL', 'REACTION'],
  intents: [
    'GUILDS',
    'GUILD_MESSAGES',
    'DIRECT_MESSAGES',
    'GUILD_MESSAGE_REACTIONS',
  ],
});
const rashersClient = new Discord.Client({
  partials: ['MESSAGE', 'CHANNEL', 'REACTION'],
  intents: [
    'GUILDS',
    'GUILD_MESSAGES',
    'DIRECT_MESSAGES',
    'GUILD_MESSAGE_REACTIONS',
  ],
});
const { MongoClient } = require('mongodb');
const winston = require('winston');
const request = require('request');
const http = require('http');
const translate = require('deepl');
const axios = require('axios').default;
const { v4: uuidv4 } = require('uuid');

const freeTranslate = require('free-translate');

var logger = '';
var access_token = '';
const databaseName = process.env.DATABASE_NAME;

var Twit = require('twit');
var T = new Twit({
  consumer_key: process.env.TWITTER_CONSUMER_KEY,
  consumer_secret: process.env.TWITTER_CONSUMER_SECRET,
  access_token: process.env.TWITTER_ACCESS_TOKEN,
  access_token_secret: process.env.TWITTER_ACCESS_TOKEN_SECRET,
  timeout_ms: 60 * 1000, // optional HTTP request timeout to apply to all requests.
  strictSSL: true, // optional - requires SSL certificates to be valid.
});

var appPropertyList = [];

var tierTwitterDict = {};
var bannedSourceDict = {};
var bannedUrlDict = {};
var twitterUserIdsDict = {};
var dupMessageTimeoutDict = {};
var latestSpotifyPodcastEpisodeDict = {};
var dupLinkChannelsDict = {};
var bannedUrlChannelsDict = {};
var tweetTranslateChannelsDict = {};
var tierChannelsDict = {};
var tierSearchChannelsDict = {};
var rasherMsgIds = new Set();

const utils = require('./utils/utils');
const messageHelper = require('./src/helper/message/messageHelper');
const tierHelper = require('./src/helper/tier/tierHelper');
const bannedSourceHelper = require('./src/helper/bannedSource/bannedSource.js');
const bannedUrlHelper = require('./src/helper/bannedUrl/bannedUrl.js');
const rashersBoardHelper = require('./src/helper/rashersboard/rashersBoardHelper');

const { Mongoose } = require('mongoose');
const { match } = require('assert');

var stream;

var stringSimilarity = require('string-similarity');

/*
RashersBoard Code Setup
*/
let settings;
let rashersdb;
let guildID = '';
let smugboardID = '';
let messagePosted = {};
let loading = true;

client.login(process.env.CLIENT_TOKEN);
rashersClient.login(process.env.RASHERS_CLIENT_TOKEN);

client.on('ready', () => {
  logger = winston.createLogger({
    transports: [new winston.transports.Console()],
  });
  getAllTiers();
  getAllBannedUrls();
  getAllBannedSources();
  getAllDupLinkRemovalChannels();
  getAllBannedUrlChannels();
  getAllTweetTranslateChannels();
  getAllTierReplyChannels();
  getServerAppProperties();
  getTweets();
  getAllTierSearchChannels();
  configureSpotify();
  loadAllPreviousMessagesFromChannel();

  logger.info(`Logged in as ${client.user.tag}!`);
});

rashersClient.on('ready', () => {
  logger = winston.createLogger({
    transports: [new winston.transports.Console()],
  });
  //Rashers Setup
  setupRashers();
  getAllRasherMsgIds();
  logger.info(`Logged in as ${rashersClient.user.tag}!`);
});

client.on('messageCreate', (msg) => {
  if (msg.author.bot) return;
  if (!msg.guild) return;

  const channelID = msg.channel.id ? msg.channel.id : '';
  const serverID = msg.guild.id ? msg.guild.id : '';
  const serverName = msg.guild.name ? msg.guild.name : '';
  const messageID = msg.id;

  const userID = msg.author.id;
  const user = client.users.fetch(userID);

  var lowerCaseMessage = msg.toString();

  try {
    if (
      msg.content.startsWith(process.env.REFRESH_CACHE_COMMAND) &&
      msg.member.permissions.has(process.env.ADMIN_PERMISSION)
    )
      refreshCache();
    if (
      msg.content.startsWith(process.env.DUP_MSG_TIMEOUT_COMMAND) &&
      msg.member.permissions.has(process.env.ADMIN_PERMISSION)
    )
      insertDupMessageTimeoutForServer(serverID, msg);
    if (
      msg.content.startsWith(
        process.env.NEW_TWITTER_USER_ID_TO_FOLLOW_COMMAND
      ) &&
      msg.member.permissions.has(process.env.ADMIN_PERMISSION)
    )
      insertNewTwitterUserId(msg);
    if (
      msg.content.startsWith(
        process.env.REMOVE_TWITTER_USER_ID_TO_FOLLOW_COMMAND
      ) &&
      msg.member.permissions.has(process.env.ADMIN_PERMISSION)
    )
      removeTwitterUserId(msg);
    if (
      msg.content.startsWith(process.env.NEW_PODCAST_TO_FOLLOW_COMMAND) &&
      msg.member.permissions.has(process.env.ADMIN_PERMISSION)
    )
      findAndInsertPodcast(msg);
    if (
      msg.content.startsWith(process.env.PODCAST_HELP_COMMAND) &&
      msg.member.permissions.has(process.env.ADMIN_PERMISSION)
    )
      podcastHelp(msg);
    if (
      msg.content.startsWith(process.env.REMOVE_PODCAST_TO_FOLLOW_COMMAND) &&
      msg.member.permissions.has(process.env.ADMIN_PERMISSION)
    )
      removeFollowingPodcast(msg);
    if (
      msg.content.startsWith(process.env.NEW_TIER_TO_ADD_COMMAND) &&
      msg.member.permissions.has(process.env.ADMIN_PERMISSION)
    )
      insertOrUpdateTier(msg);
    if (
      msg.content.startsWith(process.env.UPDATE_TIER_TO_ADD_COMMAND) &&
      msg.member.permissions.has(process.env.ADMIN_PERMISSION)
    )
      updateTier(msg);
    if (
      msg.content.startsWith(process.env.REMOVE_TIER_TO_ADD_COMMAND) &&
      msg.member.permissions.has(process.env.ADMIN_PERMISSION)
    )
      removeTier(msg);
    if (
      (msg.content.startsWith(process.env.GET_TIER_COMMAND) &&
        msg.member.permissions.has(process.env.ADMIN_PERMISSION)) ||
      (msg.content.startsWith(process.env.GET_TIER_COMMAND) &&
        msg.channel.id in tierSearchChannelsDict)
    )
      getTier(msg);
    if (
      msg.content.startsWith(process.env.NEW_BANNED_SOURCE_TO_ADD_COMMAND) &&
      msg.member.permissions.has(process.env.ADMIN_PERMISSION)
    )
      insertOrUpdateBannedSource(msg);
    if (
      msg.content.startsWith(process.env.NEW_BANNED_LINK_TO_ADD_COMMAND) &&
      msg.member.permissions.has(process.env.ADMIN_PERMISSION)
    )
      insertOrUpdateBannedLink(msg);
    if (
      msg.content.startsWith(process.env.ENABLE_DUP_LINK_REMOVAL_COMMMAND) &&
      msg.member.permissions.has(process.env.ADMIN_PERMISSION)
    )
      insertOrUpdateDupLinkRemovalChannel(msg);
    if (
      msg.content.startsWith(process.env.ENABLE_BANNED_URL_REMOVAL_COMMMAND) &&
      msg.member.permissions.has(process.env.ADMIN_PERMISSION)
    )
      insertOrUpdateBannedUrlRemovalChannel(msg);
    if (
      msg.content.startsWith(process.env.ENABLE_TWEET_TRANSLATIONS_COMMMAND) &&
      msg.member.permissions.has(process.env.ADMIN_PERMISSION)
    )
      insertOrUpdateTweetTranslateChannel(msg);
    if (
      msg.content.startsWith(process.env.ENABLE_TIER_REPLY_COMMMAND) &&
      msg.member.permissions.has(process.env.ADMIN_PERMISSION)
    )
      insertOrUpdateTierReplyChannel(msg);
    if (
      msg.content.startsWith(process.env.ENABLE_TIER_SEARCH_COMMAND) &&
      msg.member.permissions.has(process.env.ADMIN_PERMISSION)
    ) {
      insertOrUpdateTierSearchChannel(msg);
    }

    if (
      (utils.isURL(lowerCaseMessage) &&
        !msg.member.permissions.has(process.env.ADMIN_PERMISSION)) ||
      (utils.isURL(lowerCaseMessage) &&
        msg.guild.id == process.env.TEST_SERVER_ID)
    ) {
      var matches = lowerCaseMessage.match(/\bhttps?:\/\/\S+/gi);
      var messageWithoutUrl = lowerCaseMessage.replace(
        /(?:https?|ftp):\/\/[\n\S]+/g,
        ''
      );

      for (var matchedUrl of matches) {
        matchedUrl = matchedUrl.toString().trim();

        if (matchedUrl.indexOf('mobile.') > -1) {
          matchedUrl = matchedUrl.replace('mobile.', '');
          logger.info('We have replaced the mobile aspect: ' + matchedUrl);
        }

        if (matchedUrl.indexOf('twxtter.') > -1) {
          matchedUrl = matchedUrl.replace('twxtter.', 'twitter.');
          logger.info('We have replaced the twxtter aspect: ' + matchedUrl);
        }

        if (matchedUrl.indexOf(process.env.TWITTER_URL) != -1) {
          matchedUrl = utils.removeParams(matchedUrl);
        }
        var tweetInformation = utils.getTweetInformationFromUrl(matchedUrl);
        var twitterUrl = '';
        var twitterUsername = '';
        var twitterId = '';

        if (tweetInformation != null) {
          twitterUrl = tweetInformation.twitterUrl
            ? tweetInformation.twitterUrl.toLowerCase()
            : '';
          twitterUsername = tweetInformation.twitterUsername
            ? tweetInformation.twitterUsername.toLowerCase()
            : '';
          twitterId = tweetInformation.twitterId
            ? tweetInformation.twitterId.toLowerCase()
            : '';

          if (
            twitterUsername + '_' + serverID in bannedSourceDict &&
            msg.channel.id in bannedUrlChannelsDict
          ) {
            messageHelper.deleteMsg(msg);
            var bannedSourceObj =
              bannedSourceDict[twitterUsername + '_' + serverID];
            var msgToSend =
              process.env.BLOCK_EMOJI_ID +
              ' We do not allow messages from: ' +
              twitterUsername +
              '\n\nReason: ' +
              bannedSourceObj.reason;
            messageHelper.sendBannedSourceEmbedMessage(msg, msgToSend);

            client.channels.cache
              .get(process.env.LOGS_CHANNEL_ID)
              .send(
                msg.author.toString() +
                  ' tried to send: ' +
                  msg.content.toString()
              );
            return;
          }
        }
        let domain = new URL(matchedUrl);
        domain = domain.hostname.replace('www.', '');
        if (
          domain + '_' + serverID in bannedUrlDict &&
          msg.channel.id in bannedUrlChannelsDict
        ) {
          messageHelper.deleteMsg(msg);
          var msgToSend =
            process.env.BLOCK_EMOJI_ID +
            ' Sorry: ' +
            msg.author.toString() +
            ' we do not allow messages from that url';
          messageHelper.sendBannedSourceEmbedMessage(msg, msgToSend);
          return;
        }
        var linkMetadataObj = {
          channelID: channelID,
          serverID: serverID,
          serverName: serverName,
          messageID: messageID,
          msg: msg,
          userID: userID,
          user: user,
          twitterUsername: twitterUsername,
          twitterUrl: twitterUrl,
          twitterId: twitterId,
          matchedUrl: matchedUrl,
          messageWithoutUrl: messageWithoutUrl,
        };

        insertOrUpdateLink(linkMetadataObj);
      }
    }
  } catch (e) {
    logger.error(e.message);
  }
});

function refreshCache() {
  getAllTiers();
  getAllBannedUrls();
  getAllBannedSources();
  getAllDupLinkRemovalChannels();
  getAllBannedUrlChannels();
  getAllTweetTranslateChannels();
  getAllTierChannels();
  getServerAppProperties();
  getTweets();
  configureSpotify();
  loadAllPreviousMessagesFromChannel();
  logger.info('Cache has been refreshed successfully!');
}

function setupRashers() {
  // load settings.json
  try {
    settings = require('./config/settings.json');
  } catch (e) {
    console.log(`a settings.json file has not been generated. ${e.stack}`);
    process.exit();
  }

  if (!settings.embedEmoji) settings.embedEmoji = '⭐';
  guildID = settings.serverID;
  smugboardID = settings.channelID;
}

function updatePreviousPostedLink(channelID, messageID) {
  var fullUrl =
    'https://discord.com/api/v8/channels/' +
    channelID +
    '/messages/' +
    messageID;
  var options = {
    uri: fullUrl,
    method: 'PATCH',
    headers: { Authorization: 'Bot ' + process.env.CLIENT_TOKEN },
    json: {
      flags: 4,
    },
  };
  request(options, function (error, response, body) {
    logger.debug(body);
  });
}

function insertOrUpdateLink(linkMetadataObj) {
  MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
    if (err) throw err;
    var dbo = db.db(databaseName);
    var collectionName = process.env.GREGG_LINK_COLLECTION;
    if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
    if (linkMetadataObj.msg.channel.id in dupLinkChannelsDict) {
      dbo.collection(collectionName).findOneAndUpdate(
        {
          url: linkMetadataObj.matchedUrl + linkMetadataObj.channelID,
          serverID: linkMetadataObj.serverID,
        },
        {
          $set: { updateDate: utils.getCurrentDateTime() },
          $inc: { count: 1 },
          $setOnInsert: {
            url: linkMetadataObj.matchedUrl + linkMetadataObj.channelID,
            messageLink:
              'https://discord.com/channels/' +
              linkMetadataObj.serverID +
              '/' +
              linkMetadataObj.channelID +
              '/' +
              linkMetadataObj.messageID,
            entryDate: utils.getCurrentDateTime(),
            serverID: linkMetadataObj.serverID,
          },
        },
        { upsert: true, returnDocument: 'before' },
        function (err, res) {
          if (err) throw err;
          var updatedObj = res.value;
          if (
            !updatedObj &&
            linkMetadataObj.msg.channel.id in tierChannelsDict
          ) {
            var tierObj =
              tierTwitterDict[
                linkMetadataObj.twitterUsername + '_' + linkMetadataObj.serverID
              ];
            if (
              tierObj &&
              tierObj.tier &&
              tierObj.serverID == linkMetadataObj.serverID
            ) {
              var messageToSend =
                '```' +
                'Tier for ' +
                linkMetadataObj.twitterUsername +
                ': ' +
                tierObj.tier +
                '```';
              messageHelper.replyToLinkWithEmbed(
                linkMetadataObj.msg,
                messageToSend,
                process.env.GREGG_REPLY_MSG_TIER
              );
            }
            getAdditionalTwitterAccountsTier(
              linkMetadataObj.msg,
              linkMetadataObj.twitterId
            );
            if (linkMetadataObj.msg.channel.id in tweetTranslateChannelsDict) {
              getAzureTranslatedTextForTweet(
                linkMetadataObj.msg,
                linkMetadataObj.twitterId
              );
            }
          } else if (
            !updatedObj &&
            linkMetadataObj.msg.channel.id in tweetTranslateChannelsDict
          ) {
            getAzureTranslatedTextForTweet(
              linkMetadataObj.msg,
              linkMetadataObj.twitterId
            );
          }

          const dupMsgTimeout = dupMessageTimeoutDict[linkMetadataObj.serverID]
            ? dupMessageTimeoutDict[linkMetadataObj.serverID]
            : process.env.DEFAULT_DUP_MSG_TIMEOUT;
          var totalMinutesPassed;
          if (updatedObj)
            totalMinutesPassed = Math.floor(
              utils.diff_seconds(
                updatedObj.updateDate,
                utils.getCurrentDateTime()
              ) / 60
            );

          if (
            updatedObj &&
            updatedObj.count >= 1 &&
            linkMetadataObj.messageWithoutUrl &&
            totalMinutesPassed <= dupMsgTimeout
          ) {
            updatePreviousPostedLink(
              linkMetadataObj.channelID,
              linkMetadataObj.messageID
            );
          } else if (
            updatedObj &&
            updatedObj.count >= 1 &&
            totalMinutesPassed <= dupMsgTimeout
          ) {
            messageHelper.deleteMsg(linkMetadataObj.msg);
            messageHelper.duplicateLinkSendMsg(
              linkMetadataObj.msg,
              linkMetadataObj.twitterUsername,
              updatedObj.count,
              linkMetadataObj.matchedUrl,
              updatedObj.messageLink
            );
          }

          db.close();
        }
      );
    } else if (linkMetadataObj.msg.channel.id in tierChannelsDict) {
      var tierObj =
        tierTwitterDict[
          linkMetadataObj.twitterUsername + '_' + linkMetadataObj.serverID
        ];
      if (
        tierObj &&
        tierObj.tier &&
        tierObj.serverID == linkMetadataObj.serverID
      ) {
        var messageToSend =
          '```' +
          'Tier for ' +
          linkMetadataObj.twitterUsername +
          ': ' +
          tierObj.tier +
          '```';
        messageHelper.replyToLinkWithEmbed(
          linkMetadataObj.msg,
          messageToSend,
          process.env.GREGG_REPLY_MSG_TIER
        );
      }
      getAdditionalTwitterAccountsTier(
        linkMetadataObj.msg,
        linkMetadataObj.twitterId
      );
      if (linkMetadataObj.msg.channel.id in tweetTranslateChannelsDict) {
        getAzureTranslatedTextForTweet(
          linkMetadataObj.msg,
          linkMetadataObj.twitterId
        );
      }
    } else if (linkMetadataObj.msg.channel.id in tweetTranslateChannelsDict) {
      getAzureTranslatedTextForTweet(
        linkMetadataObj.msg,
        linkMetadataObj.twitterId
      );
    }
  });
}

async function getAllTiers() {
  const client = new MongoClient(process.env.MONGODB_SRV);
  try {
    await client.connect();
    const database = client.db(process.env.DATABASE_NAME);
    database
      .collection(process.env.GREGG_TIER_LIST_COLLECTION)
      .find({})
      .toArray(function (err, result) {
        if (err) throw err;
        client.close();
        updateTierTwitterDict(result);
      });
  } finally {
  }
}

async function updateTierTwitterDict(tierList) {
  tierTwitterDict = {};
  tierList.forEach(function (tierObj) {
    if (tierObj.twitterHandle != '') {
      tierTwitterDict[tierObj.twitterHandle + '_' + tierObj.serverID] = {
        twitterHandle: tierObj.twitterHandle,
        tier: tierObj.tier,
        serverID: tierObj.serverID,
      };
    }
  });
}

async function insertOrUpdateTier(msg) {
  var msgArr = msg.content.toString().split(process.env.SEPERATOR);
  if (msgArr.length != 4) {
    messageHelper.deleteMsg(msg);
    var messageToSend =
      '```New Source not added! Incorrect Format.\nCorrect Format:' +
      process.env.NEW_TIER_TO_ADD_COMMAND +
      '-<Tier Name>-<Tier Twitter Handle>-<Tier Number/Ranking>\nExample: ' +
      process.env.NEW_TIER_TO_ADD_COMMAND +
      '-Simon Stone-sistoney67-1 (BBC/Manchester United)```';
    messageHelper.sendMessage(msg, messageToSend);
    return;
  }
  var source = msgArr[1];
  var twitterHandle = msgArr[2];
  var tier = msgArr[3];
  if (source.length == 0 || tier.length == 0) {
    messageHelper.deleteMsg(msg);
    var messageToSend =
      '```New Source not added! Incorrect Format. Tier Name and Tier are required```';
    messageHelper.sendMessage(msg, messageToSend);
    return;
  }

  MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
    if (err) throw err;
    var dbo = db.db(databaseName);
    var collectionName = process.env.GREGG_TIER_LIST_COLLECTION;
    if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
    dbo.collection(collectionName).findOneAndUpdate(
      {
        source: source,
        serverID: msg.guild.id,
      },
      {
        $set: { tier: tier, twitterHandle: twitterHandle },
        $setOnInsert: {
          source: source,
          serverID: msg.guild.id,
        },
      },
      { upsert: true, returnDocument: 'after' },
      function (err, res) {
        if (err) throw err;
        messageHelper.deleteMsg(msg);
        var messageToSend =
          '```Source added! Source: ' + source + ' with tier ' + tier + '```';
        messageHelper.sendMessage(msg, messageToSend);
        getAllTiers();
        db.close();
      }
    );
  });
}

async function updateTier(msg) {
  var msgArr = msg.content.toString().split('-');
  if (msgArr.length != 4) {
    messageHelper.deleteMsg(msg);
    var messageToSend =
      '```Source not updated! Incorrect Format.\nCorrect Format:' +
      process.env.UPDATE_TIER_TO_ADD_COMMAND +
      '-<Tier Name>-<Tier Twitter Handle>-<Tier Number/Ranking>\nExample: ' +
      process.env.UPDATE_TIER_TO_ADD_COMMAND +
      '-Simon Stone-sistoney67-1 (BBC/Manchester United)```';
    messageHelper.sendMessage(msg, messageToSend);
    return;
  }
  var source = msgArr[1];
  var twitterHandle = msgArr[2];
  var tier = msgArr[3];
  if (source.length == 0 || tier.length == 0) {
    messageHelper.deleteMsg(msg);
    var messageToSend =
      '```Source not updated! Incorrect Format. Tier Name and Tier are required```';
    messageHelper.sendMessage(msg, messageToSend);
    return;
  }

  MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
    if (err) throw err;
    var dbo = db.db(databaseName);
    var collectionName = process.env.GREGG_TIER_LIST_COLLECTION;
    if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
    dbo.collection(collectionName).updateOne(
      {
        source: source,
        serverID: msg.guild.id,
      },
      {
        $set: {
          tier: tier,
          twitterHandle: twitterHandle,
          source: source,
          serverID: msg.guild.id,
        },
      },
      { upsert: false, returnDocument: 'after' },
      function (err, res) {
        if (err) throw err;
        messageHelper.deleteMsg(msg);
        console.log(res);
        if (res.modifiedCount > 0) {
          var messageToSend =
            '```Source updated! Source: ' +
            source +
            ' with tier ' +
            tier +
            '```';
          messageHelper.sendMessage(msg, messageToSend);
        } else {
          var messageToSend =
            '```Source' +
            source +
            ' not found and not updated! Source: ' +
            '```';
          messageHelper.sendMessage(msg, messageToSend);
        }
        getAllTiers();
        db.close();
      }
    );
  });
}

async function removeTier(msg) {
  var msgArr = msg.content.toString().split(process.env.SEPERATOR);
  if (msgArr.length != 2) {
    messageHelper.deleteMsg(msg);
    var messageToSend =
      '```Source not deleted! Incorrect Format.\nCorrect Format:' +
      process.env.REMOVE_TIER_TO_ADD_COMMAND +
      '-<Tier Name>\nExample: ' +
      process.env.REMOVE_TIER_TO_ADD_COMMAND +
      '-Simon Stone```';
    messageHelper.sendMessage(msg, messageToSend);
    return;
  }
  var source = msgArr[1];

  if (source.length == 0) {
    messageHelper.deleteMsg(msg);
    var messageToSend =
      '```Source not updated! Incorrect Format. Tier Name is required```';
    messageHelper.sendMessage(msg, messageToSend);
    return;
  }

  MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
    if (err) throw err;
    var dbo = db.db(databaseName);
    var collectionName = process.env.GREGG_TIER_LIST_COLLECTION;
    if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
    dbo.collection(collectionName).deleteOne(
      {
        source: source,
        serverID: msg.guild.id,
      },
      function (err, res) {
        if (err) throw err;
        messageHelper.deleteMsg(msg);
        console.log(res);
        if (res.deletedCount > 0) {
          var messageToSend = '```Source deleted' + '```';
          messageHelper.sendMessage(msg, messageToSend);
        } else {
          var messageToSend = '```Source not found and not deleted!' + '```';
          messageHelper.sendMessage(msg, messageToSend);
        }
        getAllTiers();
        db.close();
      }
    );
  });
}

async function getTier(msg) {
  var [first, ...source] = msg.content.toString().split(' ');
  source = source.join(' ');
  if (source.length == 0) {
    messageHelper.deleteMsg(msg);
    var messageToSend =
      '```Incorrect Format.\nCorrect Format:' +
      process.env.GET_TIER_COMMAND +
      ' <Name of source>\nExample: ' +
      process.env.GET_TIER_COMMAND +
      ' Simon Stone```';
    messageHelper.sendMessage(msg, messageToSend);
    return;
  }

  if (source.length <= 2) {
    messageHelper.deleteMsg(msg);
    var messageToSend = '```Please enter more than 2 characters for search```';
    messageHelper.sendMessage(msg, messageToSend);
    return;
  }

  const mongoClient = new MongoClient(process.env.MONGODB_SRV);
  try {
    await mongoClient.connect();
    const database = mongoClient.db(process.env.DATABASE_NAME);
    database
      .collection(process.env.GREGG_TIER_LIST_COLLECTION)
      .find({ source: new RegExp(source, 'i'), serverID: msg.guild.id })
      .toArray(function (err, result) {
        mongoClient.close();
        if (err) throw err;
        if (result.length == 0) {
          messageHelper.deleteMsg(msg);
          var messageToSend = 'Tier does not exist for :' + source;
          messageHelper.sendTierEmbedMessage(msg, source, messageToSend);
          return;
        }
        var tierList = [];
        result.forEach(function (tierObj) {
          if (tierObj.twitterHandle)
            tierList.push(
              '[' +
                tierObj.source +
                ']' +
                '(https://twitter.com/' +
                tierObj.twitterHandle +
                '): Tier: ' +
                tierObj.tier
            );
          else tierList.push(tierObj.source + ': Tier: ' + tierObj.tier);
        });
        messageHelper.sendTierEmbedMessage(msg, source, tierList.join('\n'));
        client.channels.cache
          .get(process.env.LOGS_CHANNEL_ID)
          .send(
            msg.author.toString() +
              ' tried to get a tier: ' +
              msg.content.toString()
          );
      });
  } catch (e) {
  } finally {
    return;
  }
}

async function updateBannedSourceDict(bannedSourceList) {
  bannedSourceDict = {};
  bannedSourceList.forEach(function (bannedSourceObj) {
    if (bannedSourceObj.twitterHandle != '') {
      bannedSourceDict[
        bannedSourceObj.twitterHandle + '_' + bannedSourceObj.serverID
      ] = {
        url: bannedSourceObj.url,
        serverID: bannedSourceObj.serverID,
        reason: bannedSourceObj.reason,
      };
    }
  });
}

async function updateBannedUrlDict(bannedUrlList) {
  bannedUrlDict = {};
  bannedUrlList.forEach(function (bannedUrlObj) {
    if (bannedUrlObj.url != '') {
      bannedUrlDict[bannedUrlObj.url + '_' + bannedUrlObj.serverID] = {
        url: bannedUrlObj.url,
        serverID: bannedUrlObj.serverID,
      };
    }
  });
}

async function insertOrUpdateBannedSource(msg) {
  var message = msg.content
    .toString()
    .toLowerCase()
    .replace(process.env.NEW_BANNED_SOURCE_TO_ADD_COMMAND, '')
    .trim();
  var twitterUrl = '';
  var reason = '';
  try {
    twitterUrl = message.substring(0, message.indexOf(' '));
    reason = message.substring(message.indexOf(' ') + 1);
  } catch (e) {
    logger.error(e.message);
    messageHelper.deleteMsg(msg);
    var messageToSend =
      '```Banned Source not added! Incorrect Format.\nCorrect Format:' +
      process.env.NEW_BANNED_SOURCE_TO_ADD_COMMAND +
      ' <Twitter Url> <Reason>\nExample: ' +
      process.env.NEW_BANNED_SOURCE_TO_ADD_COMMAND +
      ' twitter.com/twitter Trolling```';
    messageHelper.sendMessage(msg, messageToSend);
    return;
  }
  console.log(twitterUrl);
  if (twitterUrl.length == 0) {
    messageHelper.deleteMsg(msg);
    var messageToSend =
      '```Banned Source not added! Incorrect Format. Valid Twitter Url required```';
    messageHelper.sendMessage(msg, messageToSend);
    return;
  }
  var twitterUser = twitterUrl.split('/')[1];
  if (twitterUser.length == 0) {
    messageHelper.deleteMsg(msg);
    var messageToSend =
      '```Banned Source not added! Incorrect Format. Valid Twitter Url required```';
    messageHelper.sendMessage(msg, messageToSend);
    return;
  }

  MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
    if (err) throw err;
    var dbo = db.db(databaseName);
    var collectionName = process.env.GREGG_BANNED_SOURCE_COLLECTION;
    if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
    dbo.collection(collectionName).findOneAndUpdate(
      {
        url: twitterUrl,
        serverID: msg.guild.id,
        twitterHandle: twitterUser,
      },
      {
        $setOnInsert: {
          url: twitterUrl,
          twitterHandle: twitterUser,
          serverID: msg.guild.id,
          reason: reason,
        },
      },
      { new: true, upsert: true, returnDocument: 'after' },
      function (err, res) {
        if (err) throw err;
        messageHelper.deleteMsg(msg);
        var messageToSend = 'New Banned Source: ' + twitterUser;
        messageHelper.sendEmbedMessage(msg, messageToSend);
        getAllBannedSources();
        db.close();
      }
    );
  });
}

async function insertOrUpdateBannedLink(msg) {
  var msgArr = msg.content.toString().toLowerCase().trim().split(' ');
  if (msgArr.length != 2) {
    messageHelper.deleteMsg(msg);
    var messageToSend =
      '```Banned Url not added! Incorrect Format.\nCorrect Format:' +
      process.env.NEW_BANNED_LINK_TO_ADD_COMMAND +
      ' <Url>\nExample: ' +
      process.env.NEW_BANNED_LINK_TO_ADD_COMMAND +
      ' bit.ly```';
    messageHelper.sendMessage(msg, messageToSend);
    return;
  }
  var url = msgArr[1];
  if (url.length == 0) {
    messageHelper.deleteMsg(msg);
    var messageToSend =
      '```Banned Url not added! Incorrect Format. Valid Url required```';
    messageHelper.sendMessage(msg, messageToSend);
    return;
  }

  MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
    if (err) throw err;
    var dbo = db.db(databaseName);
    var collectionName = process.env.GREGG_BANNED_URL_COLLECTION;
    if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
    dbo.collection(collectionName).findOneAndUpdate(
      {
        url: url,
        serverID: msg.guild.id,
      },
      {
        $setOnInsert: {
          url: url,
          serverID: msg.guild.id,
        },
      },
      { new: true, upsert: true, returnDocument: 'after' },
      function (err, res) {
        if (err) throw err;
        messageHelper.deleteMsg(msg);
        var messageToSend = 'New Banned Link: ' + url;
        messageHelper.sendEmbedMessage(msg, messageToSend);
        getAllBannedUrls();
        db.close();
      }
    );
  });
}

async function updateDupLinkRemovalChannels(dupLinkChannels) {
  dupLinkChannelsDict = {};
  dupLinkChannels.forEach(function (dupLinkChannel) {
    if (dupLinkChannel.channelID != '') {
      dupLinkChannelsDict[dupLinkChannel.channelID] = {
        serverID: dupLinkChannel.serverID,
      };
    }
  });
}

async function updateBannedUrlRemovalChannels(bannedUrlChannels) {
  bannedUrlChannelsDict = {};
  bannedUrlChannels.forEach(function (bannedUrlChannel) {
    if (bannedUrlChannel.channelID != '') {
      bannedUrlChannelsDict[bannedUrlChannel.channelID] = {
        serverID: bannedUrlChannel.serverID,
      };
    }
  });
}

async function updateTweetTranslateChannels(tweetTranslateChannels) {
  tweetTranslateChannelsDict = {};
  tweetTranslateChannels.forEach(function (tweetTranslateChannel) {
    if (tweetTranslateChannel.channelID != '') {
      tweetTranslateChannelsDict[tweetTranslateChannel.channelID] = {
        serverID: tweetTranslateChannel.serverID,
      };
    }
  });
}

async function updateTierChannels(tierChannels) {
  tierChannelsDict = {};
  tierChannels.forEach(function (tierChannel) {
    if (tierChannel.channelID != '') {
      tierChannelsDict[tierChannel.channelID] = {
        serverID: tierChannel.serverID,
      };
    }
  });
}

async function updateTierSearchChannels(tierSearchChannels) {
  tierSearchChannelsDict = {};
  tierSearchChannels.forEach(function (tierSearchChannel) {
    if (tierSearchChannel.channelID != '') {
      tierSearchChannelsDict[tierSearchChannel.channelID] = {
        serverID: tierSearchChannel.serverID,
      };
    }
  });
}

async function insertOrUpdateDupLinkRemovalChannel(msg) {
  MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
    if (err) throw err;
    var dbo = db.db(databaseName);
    var collectionName = process.env.GREGG_DUPLICATE_LINK_REMOVAL_CHANNEL;
    if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
    dbo.collection(collectionName).findOneAndUpdate(
      {
        serverID: msg.guild.id,
        channelID: msg.channel.id,
      },
      {
        $setOnInsert: {
          serverID: msg.guild.id,
          channelID: msg.channel.id,
        },
      },
      { new: true, upsert: true, returnDocument: 'after' },
      function (err, res) {
        if (err) throw err;
        messageHelper.deleteMsg(msg);
        var messageToSend = 'Channel will now remove duplicate links. Enjoy!';
        messageHelper.sendEmbedMessage(msg, messageToSend);
        getAllDupLinkRemovalChannels();
        db.close();
      }
    );
  });
}

async function insertOrUpdateBannedUrlRemovalChannel(msg) {
  MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
    if (err) throw err;
    var dbo = db.db(databaseName);
    var collectionName = process.env.GREGG_BANNED_URL_REMOVAL_CHANNEL;
    if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
    dbo.collection(collectionName).findOneAndUpdate(
      {
        serverID: msg.guild.id,
        channelID: msg.channel.id,
      },
      {
        $setOnInsert: {
          serverID: msg.guild.id,
          channelID: msg.channel.id,
        },
      },
      { new: true, upsert: true, returnDocument: 'after' },
      function (err, res) {
        if (err) throw err;
        messageHelper.deleteMsg(msg);
        var messageToSend =
          'Channel will now remove banned tweets/urls. Enjoy!';
        messageHelper.sendEmbedMessage(msg, messageToSend);
        getAllBannedUrlChannels();
        db.close();
      }
    );
  });
}

async function insertOrUpdateTweetTranslateChannel(msg) {
  MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
    if (err) throw err;
    var dbo = db.db(databaseName);
    var collectionName = process.env.GREGG_ENABLE_TWEET_TRANSLATIONS_CHANNEL;
    if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
    dbo.collection(collectionName).findOneAndUpdate(
      {
        serverID: msg.guild.id,
        channelID: msg.channel.id,
      },
      {
        $setOnInsert: {
          serverID: msg.guild.id,
          channelID: msg.channel.id,
        },
      },
      { new: true, upsert: true, returnDocument: 'after' },
      function (err, res) {
        if (err) throw err;
        messageHelper.deleteMsg(msg);
        var messageToSend = 'Channel will now translate tweets. Enjoy!';
        messageHelper.sendEmbedMessage(msg, messageToSend);
        getAllTweetTranslateChannels();
        db.close();
      }
    );
  });
}

async function insertOrUpdateTierReplyChannel(msg) {
  MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
    if (err) throw err;
    var dbo = db.db(databaseName);
    var collectionName = process.env.GREGG_ENABLE_TIERS_CHANNEL;
    if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
    dbo.collection(collectionName).findOneAndUpdate(
      {
        serverID: msg.guild.id,
        channelID: msg.channel.id,
      },
      {
        $setOnInsert: {
          serverID: msg.guild.id,
          channelID: msg.channel.id,
        },
      },
      { new: true, upsert: true, returnDocument: 'after' },
      function (err, res) {
        if (err) throw err;
        messageHelper.deleteMsg(msg);
        var messageToSend = 'Channel will now display tiers. Enjoy!';
        messageHelper.sendEmbedMessage(msg, messageToSend);
        getAllTierReplyChannels();
        db.close();
      }
    );
  });
}

async function insertOrUpdateTierSearchChannel(msg) {
  console.log('!enabletier');
  MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
    if (err) throw err;
    var dbo = db.db(databaseName);
    var collectionName = process.env.GREGG_ENABLE_TIER_SEARCH_CHANNEL;
    if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
    dbo.collection(collectionName).findOneAndUpdate(
      {
        serverID: msg.guild.id,
        channelID: msg.channel.id,
      },
      {
        $setOnInsert: {
          serverID: msg.guild.id,
          channelID: msg.channel.id,
        },
      },
      { new: true, upsert: true, returnDocument: 'after' },
      function (err, res) {
        if (err) throw err;
        messageHelper.deleteMsg(msg);
        var messageToSend =
          'Channel will now dislay tier search results. Enjoy!';
        messageHelper.sendEmbedMessage(msg, messageToSend);
        getAllTierSearchChannels();
        db.close();
      }
    );
  });
}

async function getAllBannedSources() {
  const client = new MongoClient(process.env.MONGODB_SRV);
  try {
    await client.connect();
    const database = client.db(process.env.DATABASE_NAME);
    database
      .collection(process.env.GREGG_BANNED_SOURCE_COLLECTION)
      .find({})
      .toArray(function (err, result) {
        if (err) throw err;
        client.close();
        updateBannedSourceDict(result);
      });
  } finally {
  }
}

async function getAllBannedUrls() {
  const client = new MongoClient(process.env.MONGODB_SRV);
  try {
    await client.connect();
    const database = client.db(process.env.DATABASE_NAME);
    database
      .collection(process.env.GREGG_BANNED_URL_COLLECTION)
      .find({})
      .toArray(function (err, result) {
        if (err) throw err;
        client.close();
        updateBannedUrlDict(result);
      });
  } finally {
  }
}

async function getAllDupLinkRemovalChannels() {
  const client = new MongoClient(process.env.MONGODB_SRV);
  try {
    await client.connect();
    const database = client.db(process.env.DATABASE_NAME);
    database
      .collection(process.env.GREGG_DUPLICATE_LINK_REMOVAL_CHANNEL)
      .find({})
      .toArray(function (err, result) {
        if (err) throw err;
        client.close();
        updateDupLinkRemovalChannels(result);
      });
  } finally {
  }
}

async function getAllBannedUrlChannels() {
  const client = new MongoClient(process.env.MONGODB_SRV);
  try {
    await client.connect();
    const database = client.db(process.env.DATABASE_NAME);
    database
      .collection(process.env.GREGG_BANNED_URL_REMOVAL_CHANNEL)
      .find({})
      .toArray(function (err, result) {
        if (err) throw err;
        client.close();
        updateBannedUrlRemovalChannels(result);
      });
  } finally {
  }
}

async function getAllTweetTranslateChannels() {
  const client = new MongoClient(process.env.MONGODB_SRV);
  try {
    await client.connect();
    const database = client.db(process.env.DATABASE_NAME);
    database
      .collection(process.env.GREGG_ENABLE_TWEET_TRANSLATIONS_CHANNEL)
      .find({})
      .toArray(function (err, result) {
        if (err) throw err;
        client.close();
        updateTweetTranslateChannels(result);
      });
  } finally {
  }
}

async function getAllTierReplyChannels() {
  const client = new MongoClient(process.env.MONGODB_SRV);
  try {
    await client.connect();
    const database = client.db(process.env.DATABASE_NAME);
    database
      .collection(process.env.GREGG_ENABLE_TIERS_CHANNEL)
      .find({})
      .toArray(function (err, result) {
        if (err) throw err;
        client.close();
        updateTierChannels(result);
      });
  } finally {
  }
}

async function getAllTierSearchChannels() {
  const client = new MongoClient(process.env.MONGODB_SRV);
  try {
    await client.connect();
    const database = client.db(process.env.DATABASE_NAME);
    database
      .collection(process.env.GREGG_ENABLE_TIER_SEARCH_CHANNEL)
      .find({})
      .toArray(function (err, result) {
        if (err) throw err;
        client.close();
        updateTierSearchChannels(result);
      });
  } finally {
  }
}

async function getServerAppProperties() {
  const client = new MongoClient(process.env.MONGODB_SRV);
  try {
    await client.connect();
    const database = client.db(process.env.DATABASE_NAME);
    const appProperty = database
      .collection(process.env.GREGG_SERVER_APP_PROPERTY_COLLECTION)
      .find({})
      .toArray(function (err, result) {
        client.close();
        if (err) throw err;
        appPropertyList = result;
        getDupMessageTimeoutDict(appPropertyList);
      });
  } finally {
  }
}

async function getDupMessageTimeoutDict(appPropertyList) {
  appPropertyList.forEach(function (appPropertyObj) {
    if (appPropertyObj.dupMessageTimeout != '') {
      dupMessageTimeoutDict[appPropertyObj.serverID] =
        appPropertyObj.dupMessageTimeout;
    }
  });
}

async function insertDupMessageTimeoutForServer(serverID, msg) {
  var dupMessageTimeoutArray = msg.toString().trim().split(' ');
  if (
    dupMessageTimeoutArray.length < 2 ||
    !utils.isNumeric(dupMessageTimeoutArray[1])
  ) {
    messageHelper.deleteMsg(msg);
    var messageToSend =
      '```Update not successful! Incorrect Format.\nCorrect Format:' +
      process.env.DUP_MSG_TIMEOUT_COMMAND +
      ' <Number of minutes (15-1440)>.\nExample: ' +
      process.env.DUP_MSG_TIMEOUT_COMMAND +
      ' 15```';
    messageHelper.sendMessage(msg, messageToSend);
    return;
  } else if (
    dupMessageTimeoutArray[1] < 1 ||
    dupMessageTimeoutArray[1] > 1440
  ) {
    messageHelper.deleteMsg(msg);
    var messageToSend =
      '```Update not successful! Please select a number between 15 and 1440.\nCorrect Format:' +
      process.env.DUP_MSG_TIMEOUT_COMMAND +
      ' <Number of minutes (15-1440)>.\nExample: ' +
      process.env.DUP_MSG_TIMEOUT_COMMAND +
      ' 15```';
    messageHelper.sendMessage(msg, messageToSend);
    return;
  }

  MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
    if (err) throw err;
    var dbo = db.db(databaseName);
    var collectionName = process.env.GREGG_SERVER_APP_PROPERTY_COLLECTION;
    if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
    dbo.collection(collectionName).findOneAndUpdate(
      {
        serverID: serverID,
      },
      {
        $set: {
          updateDate: utils.getCurrentDateTime(),
          dupMessageTimeout: dupMessageTimeoutArray[1],
        },

        $setOnInsert: {
          serverID: serverID,
          entryDate: utils.getCurrentDateTime(),
        },
      },
      { upsert: true, returnDocument: 'after' },
      function (err, res) {
        db.close();
        if (err) throw err;
        dupMessageTimeoutDict[res.value.serverID] = res.value.dupMessageTimeout;
        messageHelper.deleteMsg(msg);
        var messageToSend =
          '```Update Successful! Now duplicate messages can be posted after: ' +
          res.value.dupMessageTimeout +
          ' minutes without being removed```';
        messageHelper.sendMessage(msg, messageToSend);
      }
    );
  });
}

function getAdditionalTwitterAccountsTier(msg, twitterId) {
  T.get(
    'statuses/show/:id',
    { id: twitterId, tweet_mode: 'extended' },
    function (err, data, response) {
      try {
        var str = data.full_text;
        var pattern = /\B@[a-z0-9_-]+/gi;
        var firstPass = str.match(pattern);
        var secondPass = str.substring(
          str.lastIndexOf('[') + 1,
          str.lastIndexOf(']')
        );
        secondPass.split(',');
        if (
          firstPass != null &&
          secondPass != null &&
          firstPass.length != 0 &&
          secondPass.length != 0
        )
          firstPass.concat(secondPass.split('/'));
        var messageToSend = '';
        if (firstPass != null) {
          for (var account of firstPass) {
            account = account.replace('@', '');
            var tierObj =
              tierTwitterDict[
                account.toLowerCase().trim() + '_' + msg.guild.id
              ];
            if (tierObj) {
              var messageToSend =
                messageToSend +
                '```' +
                'Tier for ' +
                tierObj.twitterHandle +
                ': ' +
                tierObj.tier +
                '```\n';
            }
          }
          if (messageToSend != '')
            messageHelper.replyToLinkWithEmbed(
              msg,
              messageToSend,
              process.env.GREGG_REPLY_MSG_TIER
            );
        }
      } catch (e) {}
    }
  );
}

function getDeeplTranslatedTextForTweet(msg, twitterId) {
  T.get(
    'statuses/show/:id',
    { id: twitterId, tweet_mode: 'extended' },
    function (err, data, response) {
      var tweetText = data.full_text;
      translate({
        free_api: true,
        text: tweetText,
        target_lang: process.env.DEEPL_DEFAULT_TARGET_LANG,
        auth_key: process.env.DEEPL_API_KEY,
      })
        .then((result) => {
          if (
            result.data.translations[0].detected_source_language &&
            result.data.translations[0].detected_source_language ==
              process.env.DEEPL_DEFAULT_TARGET_LANG
          )
            logger.info(
              'Valid Translation but no new language detected for: ' + tweetText
            );
          else {
            logger.debug(
              'Detected Source: ' +
                result.data.translations[0].detected_source_language +
                ' for tweet: ' +
                tweetText
            );
            var messageToSend =
              '```' +
              'Tweet Translated:\n' +
              result.data.translations[0].text +
              '```\n';
            if (messageToSend != '')
              messageHelper.replyToLinkWithEmbed(
                msg,
                messageToSend,
                process.env.GREGG_REPLY_MSG_TRANSLATION
              );
          }
        })
        .catch((error) => {
          logger.error(error);
        });
    }
  );
}

async function getAzureTranslatedTextForTweet(msg, twitterId) {
  T.get(
    'statuses/show/:id',
    { id: twitterId, tweet_mode: 'extended' },
    function (err, data, response) {
      try {
        var tweetText = data.full_text;
        tweetText = tweetText.replace('#', '');
        freeTranslate
          .translate(tweetText, { to: 'en' })
          .then((translatedText) => {
            if (
              parseFloat(
                stringSimilarity.compareTwoStrings(tweetText, translatedText)
              ) < parseFloat(process.env.SIMILAR_TEXT_PERCENTAGE)
            ) {
              var messageToSend = '```' + translatedText + '```\n';
              if (messageToSend != '')
                messageHelper.replyToLinkWithEmbed(
                  msg,
                  messageToSend,
                  process.env.GREGG_REPLY_MSG_TRANSLATION
                );
              updatePreviousPostedLink(msg.channel.id, msg.id);
              client.channels.cache
                .get(process.env.LOGS_CHANNEL_ID)
                .send(
                  'DIFFERENT TEXT: ' +
                    tweetText +
                    '\nwas not similar to\n' +
                    translatedText +
                    '\n\n' +
                    stringSimilarity.compareTwoStrings(
                      tweetText,
                      translatedText
                    )
                );
            } else {
              client.channels.cache
                .get(process.env.LOGS_CHANNEL_ID)
                .send(
                  'SIMILAR TEXT: ' +
                    tweetText +
                    '\nwas the similar to\n' +
                    translatedText +
                    '\n\n' +
                    stringSimilarity.compareTwoStrings(
                      tweetText,
                      translatedText
                    )
                );
            }
          });
      } catch (e) {
        logger.error(e.message);
        getDeeplTranslatedTextForTweet(msg, twitterId);
      }
    }
  );
}

async function insertNewTwitterUserId(msg) {
  var newTwitterUserIdArray = msg.toString().toLowerCase().trim().split(' ');
  if (
    newTwitterUserIdArray.length < 2 ||
    !utils.isNumeric(newTwitterUserIdArray[1])
  ) {
    messageHelper.deleteMsg(msg);
    var messageToSend =
      '```Update not successful! Incorrect Format.\nCorrect Format:' +
      process.env.NEW_TWITTER_USER_ID_TO_FOLLOW_COMMAND +
      ' <Twitter User Id>.\nExample: ' +
      process.env.NEW_TWITTER_USER_ID_TO_FOLLOW_COMMAND +
      ' 0000000000000000000```';
    messageHelper.sendMessage(msg, messageToSend);
    return;
  }
  var twitterUserId = newTwitterUserIdArray[1];
  MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
    if (err) throw err;
    var dbo = db.db(databaseName);
    var collectionName = process.env.GREGG_LOAD_TWEET_CHANNEL_COLLECTION;
    if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
    dbo.collection(collectionName).findOneAndUpdate(
      {
        serverID: msg.guild.id,
        channelID: msg.channel.id,
        twitterUserId: twitterUserId,
      },
      {
        $set: {
          updateDate: utils.getCurrentDateTime(),
        },
        $setOnInsert: {
          serverID: msg.guild.id,
          channelID: msg.channel.id,
          twitterUserId: twitterUserId,
          entryDate: utils.getCurrentDateTime(),
        },
      },
      { upsert: true, returnDocument: 'after' },
      function (err, res) {
        db.close();
        if (err) throw err;
        if (!twitterUserIdsDict[twitterUserId])
          twitterUserIdsDict[twitterUserId] = [];
        twitterUserIdsDict[twitterUserId].push(msg.channel.id);
        messageHelper.deleteMsg(msg);
        var messageToSend =
          '```Update Successful! Now tweets from Twitter User Id: ' +
          twitterUserId +
          ' will be posted to channel: ' +
          msg.channel.name +
          ' ```';
        messageHelper.sendMessage(msg, messageToSend);
        if (stream) stream.stop();
        streamTweets();
      }
    );
  });
}

async function removeTwitterUserId(msg) {
  var removeTwitterUserIdArray = msg.toString().toLowerCase().trim().split(' ');
  if (
    removeTwitterUserIdArray.length < 2 ||
    !utils.isNumeric(removeTwitterUserIdArray[1])
  ) {
    messageHelper.deleteMsg(msg);
    var messageToSend =
      '```Update not successful! Incorrect Format.\nCorrect Format:' +
      process.env.REMOVE_TWITTER_USER_ID_TO_FOLLOW_COMMAND +
      ' <Twitter User Id>.\nExample: ' +
      process.env.REMOVE_TWITTER_USER_ID_TO_FOLLOW_COMMAND +
      ' 0000000000000000000```';
    messageHelper.sendMessage(msg, messageToSend);
    return;
  }
  var twitterUserId = removeTwitterUserIdArray[1];

  if (!twitterUserIdsDict.hasOwnProperty(twitterUserId)) {
    messageHelper.deleteMsg(msg);
    var messageToSend = '```Twitter Account is not being followed already.```';
    messageHelper.sendMessage(msg, messageToSend);
    return;
  }
  MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
    if (err) throw err;
    var dbo = db.db(databaseName);
    var collectionName = process.env.GREGG_LOAD_TWEET_CHANNEL_COLLECTION;
    if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
    query = {
      serverID: msg.guild.id,
      channelID: msg.channel.id,
      twitterUserId: twitterUserId,
    };
    dbo.collection(collectionName).deleteOne(
      {
        serverID: msg.guild.id,
        channelID: msg.channel.id,
        twitterUserId: twitterUserId,
      },
      function (err, res) {
        db.close();
        if (err) throw err;
        twitterUserIdsDict[twitterUserId] = utils.removeElementFromArray(
          twitterUserIdsDict[twitterUserId],
          msg.channel.id
        );

        if (twitterUserIdsDict[twitterUserId].length == 0) {
          delete twitterUserIdsDict[twitterUserId];
        }
        messageHelper.deleteMsg(msg);
        var messageToSend =
          '```Update Successful! Now tweets from Twitter User Id: ' +
          twitterUserId +
          ' will not be posted to channel: ' +
          msg.channel.name +
          ' ```';
        messageHelper.sendMessage(msg, messageToSend);
        if (stream) stream.stop();
        streamTweets();
      }
    );
  });
}

async function getTweets() {
  const client = new MongoClient(process.env.MONGODB_SRV);
  try {
    await client.connect();
    const database = client.db(process.env.DATABASE_NAME);
    database
      .collection(process.env.GREGG_LOAD_TWEET_CHANNEL_COLLECTION)
      .find({})
      .toArray(function (err, result) {
        if (err) throw err;
        client.close();
        result.forEach(function (twitterUserObj) {
          if (!twitterUserIdsDict[twitterUserObj.twitterUserId])
            twitterUserIdsDict[twitterUserObj.twitterUserId] = [];
          twitterUserIdsDict[twitterUserObj.twitterUserId].push(
            twitterUserObj.channelID
          );
        });
        streamTweets();
      });
  } catch (e) {
  } finally {
  }
}

async function streamTweets() {
  if (Object.keys(twitterUserIdsDict).length == 0) {
    logger.info('No Users to stream tweets for.');
    return;
  }
  try {
    stream = T.stream('statuses/filter', {
      follow: Object.keys(twitterUserIdsDict),
    });
    stream.on('tweet', function (tweet) {
      if (
        tweet.retweeted_status ||
        tweet.in_reply_to_status_id ||
        tweet.in_reply_to_status_id_str ||
        tweet.in_reply_to_user_id ||
        tweet.in_reply_to_user_id_str ||
        tweet.in_reply_to_screen_name
      )
        return true;
      console.log(twitterUserIdsDict[tweet.user.id_str]);
      if (twitterUserIdsDict.hasOwnProperty(tweet.user.id_str)) {
        var url =
          'https://twitter.com/' +
          tweet.user.screen_name +
          '/status/' +
          tweet.id_str;

        twitterUserIdsDict[tweet.user.id_str].forEach(function (storedChannel) {
          client.channels
            .fetch(storedChannel)
            .then((channel) => {
              channel.send(url);
            })
            .catch((err) => {
              console.log(err);
            });
        });
      }
    });
  } catch (e) {}
}

async function podcastHelp(msg) {
  messageHelper.deleteMsg(msg);
  var messageToSend =
    '```How to find a Spotify Podcast ID.\n\n1. Go to the Spotify Podcast page you want to follow.\n2. Press the three horizontal dots on the Podcast information page.\n3. Press Share -> Copy Show Link.\n4. Paste Link into a notepad or something similar. The link should look something like this: https://open.spotify.com/show/1RUo52lKLha4CHlEp00000?si=61add6bc7b8e413f.\n5. The Spotify Podcast id will be the value after /show/. So for the previous example the id would be: 1RUo52lKLha4CHlEp00000 ```';
  messageHelper.sendMessage(msg, messageToSend);
}

async function findAndInsertPodcast(msg) {
  var msgArr = msg.content.toString().trim().split(' ');
  if (msgArr.length != 2) {
    messageHelper.deleteMsg(msg);
    var messageToSend =
      '```Update not successful! Incorrect Format.\nCorrect Format:' +
      process.env.NEW_PODCAST_TO_FOLLOW_COMMAND +
      ' <Spotify Podcast Id>.\nExample: ' +
      process.env.NEW_PODCAST_TO_FOLLOW_COMMAND +
      ' 48vp0aYjuSGMI1uLGh0000\nFor help on finding a Spotify Podcast Id use command: ' +
      process.env.PODCAST_HELP_COMMAND +
      '```';
    messageHelper.sendMessage(msg, messageToSend);
  }
  var podcastId = msgArr[1];
  getLatestAndInsertOrUpdateSpotifyPodcast(msg, podcastId);
}

async function getLatestAndInsertOrUpdateSpotifyPodcast(msg, podcastId) {
  var spotifyApi = new SpotifyWebApi({
    accessToken: access_token,
  });
  spotifyApi.getShow(podcastId, { market: 'US' }).then(
    function (data) {
      var podcastName = data.body.name;
      spotifyApi.getShowEpisodes(podcastId, { market: 'US' }).then(
        function (data) {
          var latestPodcastEpisodeInfo = {
            latestPodcastEpisodeTitle: data.body.items[0].name,
            latestPodcastEpisodeUrl: data.body.items[0].external_urls.spotify,
            latestPodcastEpisodeDescription: data.body.items[0].description,
            latestPodcastEpisodeImg: data.body.items[0].images[0].url,
            latestPodcastEpisodeReleaseDate: data.body.items[0].release_date,
            latestPodcastEpisodeId: data.body.items[0].id,
            latestPodcastId: podcastId,
          };
          updateOrInsertLatestPodcastInfo(
            msg,
            podcastId,
            podcastName,
            latestPodcastEpisodeInfo
          );
        },
        function (err) {
          messageHelper.deleteMsg(msg);
          var messageToSend =
            '```Unable to find podcast from id\nFor help on finding a Spotify Podcast Id use command: ' +
            process.env.PODCAST_HELP_COMMAND +
            '```';
          messageHelper.sendMessage(msg, messageToSend);
        }
      );
    },
    function (err) {
      var messageToSend =
        '```Unable to find podcast from id\nFor help on finding a Spotify Podcast Id use command: ' +
        process.env.PODCAST_HELP_COMMAND +
        '```';
      messageHelper.sendMessage(msg, messageToSend);
    }
  );
}

async function updateOrInsertLatestPodcastInfo(
  msg,
  podcastId,
  podcastName,
  latestPodcastInfo
) {
  MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
    if (err) throw err;
    var dbo = db.db(databaseName);
    var collectionName = process.env.GREGG_LOAD_PODCAST_CHANNEL_COLLECTION;
    if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
    dbo.collection(collectionName).findOneAndUpdate(
      {
        podcastID: podcastId,
        channelID: msg.channel.id,
      },
      {
        $set: { updateDate: utils.getCurrentDateTime() },
        $setOnInsert: {
          latestPodcastEpisodeTitle:
            latestPodcastInfo.latestPodcastEpisodeTitle,
          latestPodcastEpisodeUrl: latestPodcastInfo.latestPodcastEpisodeUrl,
          latestPodcastEpisodeDescription:
            latestPodcastInfo.latestPodcastEpisodeDescription,
          latestPodcastEpisodeImg: latestPodcastInfo.latestPodcastEpisodeImg,
          latestPodcastEpisodeReleaseDate:
            latestPodcastInfo.latestPodcastEpisodeReleaseDate,
          latestPodcastEpisodeId: latestPodcastInfo.latestPodcastEpisodeId,
          entryDate: utils.getCurrentDateTime(),
          serverID: msg.guild.id,
          channelID: msg.channel.id,
          podcastID: podcastId,
          podcastName: podcastName,
        },
      },
      { upsert: true, returnDocument: 'before' },
      function (err, res) {
        if (err) throw err;
        if (!res.value) {
          logger.info('Inserting brand new podcast to channel to follow');
        }
        messageHelper.deleteMsg(msg);
        var messageToSend =
          '```Latest Episodes from Podcast: ' +
          podcastName +
          ' will now be posted to this channel!' +
          '```';
        messageHelper.sendMessage(msg, messageToSend);
        getPodcasts();
      }
    );
  });
}

async function getLatestSpotifyPodcastEpisodeForPodcastId(
  latestSpotifyPodcastInfoForChannelID,
  channelID
) {
  spotifyApi
    .getShowEpisodes(latestSpotifyPodcastInfoForChannelID.latestPodcastId, {
      market: 'US',
    })
    .then(
      function (data) {
        var latestPodcastEpisodeInfo = {
          latestPodcastEpisodeTitle: data.body.items[0].name,
          latestPodcastEpisodeUrl: data.body.items[0].external_urls.spotify,
          latestPodcastEpisodeDescription: data.body.items[0].description,
          latestPodcastEpisodeImg: data.body.items[0].images[0].url,
          latestPodcastEpisodeReleaseDate: data.body.items[0].release_date,
          latestPodcastEpisodeId: data.body.items[0].id,
          latestPodcastId: latestSpotifyPodcastInfoForChannelID.latestPodcastId,
        };
        if (
          latestPodcastEpisodeInfo.latestPodcastEpisodeId &&
          latestSpotifyPodcastInfoForChannelID.latestPodcastEpisodeId !=
            latestPodcastEpisodeInfo.latestPodcastEpisodeId
        ) {
          logger.info(
            'Update Podcast:' +
              channelID +
              ': ' +
              latestSpotifyPodcastInfoForChannelID.latestPodcastEpisodeTitle +
              '-' +
              latestSpotifyPodcastInfoForChannelID.latestPodcastEpisodeUrl
          );
          updateLatestPodcastInfo(latestPodcastEpisodeInfo, channelID);
        } else {
          logger.debug(
            'Not going to update podcast in channel:' +
              channelID +
              ': ' +
              latestSpotifyPodcastInfoForChannelID.latestPodcastEpisodeTitle +
              '-' +
              latestSpotifyPodcastInfoForChannelID.latestPodcastEpisodeUrl
          );
        }
      },
      function (err) {
        logger.error(
          'Error in pulling podcast episodes for podcast id: ' +
            latestSpotifyPodcastInfoForChannelID.podcastId +
            '\n' +
            err
        );
      }
    );
}

async function postPodcast(latestPodcastInfo, channelID) {
  const embed = new Discord.MessageEmbed()
    .setImage(latestPodcastInfo.latestPodcastEpisodeImg)
    .setTitle(latestPodcastInfo.latestPodcastEpisodeTitle)
    .setDescription(
      latestPodcastInfo.latestPodcastEpisodeDescription +
        '\n\nClick below to listen.\n\n' +
        latestPodcastInfo.latestPodcastEpisodeUrl
    );
  client.channels.cache.get(channelID).send({ embeds: [embed] });
}

async function updateLatestPodcastInfo(latestPodcastInfo, channelID) {
  MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
    if (err) throw err;
    var dbo = db.db(databaseName);
    var collectionName = process.env.GREGG_LOAD_PODCAST_CHANNEL_COLLECTION;
    if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
    dbo.collection(collectionName).findOneAndUpdate(
      {
        podcastID: latestPodcastInfo.latestPodcastId,
        channelID: channelID,
      },
      {
        $set: {
          updateDate: utils.getCurrentDateTime(),
          latestPodcastEpisodeTitle:
            latestPodcastInfo.latestPodcastEpisodeTitle,
          latestPodcastEpisodeUrl: latestPodcastInfo.latestPodcastEpisodeUrl,
          latestPodcastEpisodeDescription:
            latestPodcastInfo.latestPodcastEpisodeDescription,
          latestPodcastEpisodeImg: latestPodcastInfo.latestPodcastEpisodeImg,
          latestPodcastEpisodeReleaseDate:
            latestPodcastInfo.latestPodcastEpisodeReleaseDate,
          latestPodcastEpisodeId: latestPodcastInfo.latestPodcastEpisodeId,
        },
        $setOnInsert: {
          entryDate: utils.getCurrentDateTime(),
        },
      },
      { upsert: true, returnDocument: 'before' },
      function (err, res) {
        if (err) throw err;
        if (!res.value) {
          logger.info('Inserting brand new podcast to channel to follow');
        }
        getPodcasts();
        postPodcast(latestPodcastInfo, channelID);
      }
    );
  });
}

async function checkForLatestSpotifyPodcasts() {
  for (const [key, value] of Object.entries(latestSpotifyPodcastEpisodeDict)) {
    var channelID = key;
    var latestSpotifyPodcastsInfoForChannelID = value;

    latestSpotifyPodcastsInfoForChannelID.forEach(function (
      latestSpotifyPodcastInfoForChannelID
    ) {
      try {
        getLatestSpotifyPodcastEpisodeForPodcastId(
          latestSpotifyPodcastInfoForChannelID,
          channelID
        );
      } catch (e) {
        logger.error('Error pulling in latest documents' + e);
      }
    });
  }
}

async function getPodcasts() {
  latestSpotifyPodcastEpisodeDict = {};
  const client = new MongoClient(process.env.MONGODB_SRV);
  try {
    await client.connect();
    const database = client.db(process.env.DATABASE_NAME);
    database
      .collection(process.env.GREGG_LOAD_PODCAST_CHANNEL_COLLECTION)
      .find({})
      .toArray(function (err, result) {
        if (err) throw err;
        client.close();
        result.forEach(function (latestPodcastInfoObj) {
          if (!latestSpotifyPodcastEpisodeDict[latestPodcastInfoObj.channelID])
            latestSpotifyPodcastEpisodeDict[latestPodcastInfoObj.channelID] =
              [];
          var latestPodcastEpisodeInfo = {
            latestPodcastEpisodeTitle:
              latestPodcastInfoObj.latestPodcastEpisodeTitle,
            latestPodcastEpisodeUrl:
              latestPodcastInfoObj.latestPodcastEpisodeUrl,
            latestPodcastEpisodeDescription:
              latestPodcastInfoObj.latestPodcastEpisodeDescription,
            latestPodcastEpisodeImg:
              latestPodcastInfoObj.latestPodcastEpisodeImg,
            latestPodcastEpisodeReleaseDate:
              latestPodcastInfoObj.latestPodcastEpisodeReleaseDate,
            latestPodcastEpisodeId: latestPodcastInfoObj.latestPodcastEpisodeId,
            latestPodcastId: latestPodcastInfoObj.podcastID,
          };
          latestSpotifyPodcastEpisodeDict[latestPodcastInfoObj.channelID].push(
            latestPodcastEpisodeInfo
          );
        });
      });
  } finally {
  }
}

async function configureSpotify() {
  spotifyApi = new SpotifyWebApi({
    clientId: process.env.SPOTIFY_CLIENT_ID,
    clientSecret: process.env.SPOTIFY_CLIENT_SECRET,
  });
  spotifyApi.clientCredentialsGrant().then(
    function (data) {
      access_token = data.body['access_token'];
      spotifyApi.setAccessToken(data.body['access_token']);
      getPodcasts();
    },
    function (err) {
      logger.error('Something went wrong when retrieving an access token', err);
    }
  );
}

async function updateSpotifyAccessToken() {
  spotifyApi.clientCredentialsGrant().then(
    function (data) {
      access_token = data.body['access_token'];
      spotifyApi.setAccessToken(data.body['access_token']);
      console.log(access_token);
    },
    function (err) {
      logger.error('Something went wrong when retrieving an access token', err);
    }
  );
}

async function removeFollowingPodcast(msg) {
  var removePodcastArray = msg.toString().trim().split(' ');
  if (removePodcastArray.length < 2) {
    messageHelper.deleteMsg(msg);
    var messageToSend =
      '```Update not successful! Incorrect Format.\nCorrect Format:' +
      process.env.REMOVE_PODCAST_TO_FOLLOW_COMMAND +
      ' <Spotify Podcast Id>.\nExample: ' +
      process.env.REMOVE_PODCAST_TO_FOLLOW_COMMAND +
      ' 48vp0aYjuSGMI1uLGh0000```';
    messageHelper.sendMessage(msg, messageToSend);
    return;
  }
  var spotifyPodcastId = removePodcastArray[1];
  var query = {
    podcastID: spotifyPodcastId,
    channelID: msg.channel.id,
    serverID: msg.guild.id,
  };
  MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
    if (err) throw err;
    var dbo = db.db(databaseName);
    var collectionName = process.env.GREGG_LOAD_PODCAST_CHANNEL_COLLECTION;
    if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
    dbo.collection(collectionName).deleteOne(query, function (err, res) {
      db.close();
      if (err) throw err;
      messageHelper.deleteMsg(msg);
      var messageToSend = '';
      if (!res.acknowledged) {
        messageToSend =
          '```Update Not Successful! Now Podcasts from Podcast Id: ' +
          spotifyPodcastId +
          ' will not be posted to channel: ' +
          msg.channel.name +
          ' ```';
      } else if (res.deletedCount == 0) {
        messageToSend =
          '```Update Not Successful! No Podcast with Podcast Id: ' +
          spotifyPodcastId +
          ' is configured to post to channel: ' +
          msg.channel.name +
          ' ```';
      } else
        messageToSend =
          '```Update Successful! Now Podcasts from Podcast Id: ' +
          spotifyPodcastId +
          ' will not be posted to channel: ' +
          msg.channel.name +
          ' ```';
      messageHelper.sendMessage(msg, messageToSend);
      getPodcasts();
    });
  });
}

async function loadAllPreviousMessagesFromChannel() {
  const targetChannel = client.guilds.cache
    .first()
    .channels.cache.get('934397358932906034');

  // Iterate through all the messages as they're pulled
  for await (const message of rashersBoardHelper.loadAllMessages(
    targetChannel
  )) {
    message.reactions.cache;
  }
}

var spotify_podcast_checkminutes = process.env.SPOTIFY_PODCAST_CHECK_MINUTES,
  spotify_podcast_interval = spotify_podcast_checkminutes * 60 * 1000; //This checks every x minutes, change x to whatever minute you'd like
setInterval(function () {
  try {
    logger.info('Checking for Latest Podcasts');
    checkForLatestSpotifyPodcasts();
  } catch (e) {}
}, spotify_podcast_interval);

var spotify_access_token_checkminutes =
    process.env.SPOTIFY_ACCESS_TOKEN_CHECK_MINUTES,
  spotify_access_token_interval = spotify_access_token_checkminutes * 60 * 1000; //This checks every x minutes, change x to whatever minute you'd like
setInterval(function () {
  try {
    updateSpotifyAccessToken();
  } catch (e) {}
}, spotify_access_token_interval);

var check_for_podcast_db_updates = process.env.DB_PODCAST_CHECK_MINUTES,
  podcast_db_updates_interval = check_for_podcast_db_updates * 60 * 1000; //This checks every x minutes, change x to whatever minute you'd like
setInterval(function () {
  try {
    getPodcasts();
  } catch (e) {}
}, podcast_db_updates_interval);

/*
RASHERS CODE
*/

function messageReactionRemoveHelper(reaction) {
  var msg = reaction.message;
  var message = msg.channel.messages
    .fetch(msg.id)
    .then((message) =>
      MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
        if (err) throw err;
        if (!rasherMsgIds.has(message.id)) {
          console.log('Message id not found');
          sendLogMessage(
            'Not going to proceed with rasher removal since message not tracked yet.'
          );
          return;
        }
        var dbo = db.db(databaseName);
        var collectionName = process.env.GREGG_RASHERS_COLLECTION;
        if (!dbo.collection(collectionName))
          dbo.createCollection(collectionName);
        dbo.collection(collectionName).findOneAndUpdate(
          {
            userID: message.author.id,
            serverID: message.guildId,
          },

          {
            $set: { updateDate: utils.getCurrentDateTime() },
            $inc: { count: -1 },
            $setOnInsert: {
              userID: reaction.message.author.id,
              channelID: reaction.message.channel.id,
              entryDate: utils.getCurrentDateTime(),
              serverID: reaction.message.guild.id,
            },
          },
          { upsert: true, returnDocument: 'after', count: { $gt: 0 } },
          function (err, res) {
            if (err) throw err;
            var rasherObj = res.value;
            sendLogMessage(
              message.author.username +
                ' now has a total of: ' +
                rasherObj.count +
                ' rashers'
            );
            db.close();
            logger.info('Total msg reaction count: ' + reaction.count);

            updateRashersBoard(reaction, reaction.count);
            return;
          }
        );
      })
    )
    .catch(console.error);
}

function messageReactionAddHelper(reaction) {
  var msg = reaction.message;

  var updateAmount = 1;

  if (!rasherMsgIds.has(reaction.message.id))
    updateAmount = reaction.count && reaction.count > 0 ? reaction.count : 1;

  console.log(reaction.message + ': ' + reaction.count);
  var message = msg.channel.messages
    .fetch(msg.id)
    .then((message) =>
      MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
        if (err) throw err;
        var dbo = db.db(databaseName);
        var collectionName = process.env.GREGG_RASHERS_COLLECTION;
        if (!dbo.collection(collectionName))
          dbo.createCollection(collectionName);
        dbo.collection(collectionName).findOneAndUpdate(
          {
            userID: message.author.id,
            serverID: message.guildId,
          },
          {
            $set: { updateDate: utils.getCurrentDateTime() },
            $inc: { count: updateAmount },
            $setOnInsert: {
              userID: message.author.id,
              channelID: message.channel.id,
              entryDate: utils.getCurrentDateTime(),
              serverID: message.guild.id,
            },
          },
          { upsert: true, returnDocument: 'after' },
          function (err, res) {
            if (err) throw err;

            var rasherObj = res.value;
            sendLogMessage(
              message.author.username +
                ' now has a total of: ' +
                rasherObj.count +
                ' rashers'
            );
            db.close();
            updateRashersMsgIds(reaction);
            updateRashersBoard(reaction, reaction.count);
            return;
          }
        );
      })
    )
    .catch(console.error);
}

function updateRashersMsgIds(reaction) {
  var msg = reaction.message;
  var message = msg.channel.messages
    .fetch(msg.id)
    .then((message) =>
      MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
        if (err) throw err;
        var dbo = db.db(databaseName);
        var collectionName = process.env.GREGG_RASHERS_MESSAGE_ID_COLLECTION;
        if (!dbo.collection(collectionName))
          dbo.createCollection(collectionName);
        dbo.collection(collectionName).findOneAndUpdate(
          {
            msgId: message.id,
          },
          {
            $setOnInsert: {
              msgId: message.id,
              count: reaction.count,
            },
          },
          { upsert: true, returnDocument: 'after' },
          function (err, res) {
            if (err) throw err;

            var rasherMsgIdObj = res.value;
            rasherMsgIds.add(rasherMsgIdObj.msgId);
            db.close();
            return;
          }
        );
      })
    )
    .catch(console.error);
}

// ON REACTION ADD
rashersClient.on('messageReactionAdd', (reaction, user) => {
  try {
    var channelID = '';
    var emoji = '';
    var authorId = '';
    if (reaction.partial) {
      reaction
        .fetch()
        .then((fullReaction) => {
          channelID = fullReaction.message.channel.id;
          emoji = fullReaction.emoji.name;
          authorId = fullReaction.message.author.id;

          // if channel is posting channel
          if (channelID == smugboardID) {
            logger.error('Reaction is in rashers channel');
            return;
          }
          // if reaction is not desired emoji
          if (emoji !== settings.reactionEmoji) {
            return;
          }
          //no self reacts count
          console.log(user.id + ' ' + authorId);
          if (
            user.id == authorId &&
            user.id != process.env.BYPASS_CHECKS_USER_ID
          ) {
            logger.error('Self reacts do not count');
            return;
          }

          logger.info('PARTIAL MESSAGE REACTION ADD');
          reaction
            .fetch()
            .then((fullReaction) => {
              messageReactionAddHelper(fullReaction);
            })
            .catch((error) => {
              console.log(
                'Something went wrong when fetching the message: ',
                error
              );
            });
        })
        .catch((error) => {
          console.log(
            'Something went wrong when fetching the message: ',
            error
          );
        });
    } else {
      channelID = reaction.message.channel.id;
      emoji = reaction.emoji.name;
      authorId = reaction.message.author.id;
    }
    // if channel is posting channel
    if (channelID == smugboardID) {
      logger.error('Reaction is in rashers channel');
      return;
    }
    // if reaction is not desired emoji
    if (emoji !== settings.reactionEmoji) {
      return;
    }
    //no self reacts count
    console.log(user.id + ' ' + authorId);
    if (user.id == authorId && user.id != process.env.BYPASS_CHECKS_USER_ID) {
      logger.error('Self reacts do not count');
      return;
    } else messageReactionAddHelper(reaction);
  } catch (e) {
    logger.error(e.message);
  }
});

// ON REACTION REMOVE
rashersClient.on('messageReactionRemove', (reaction, user) => {
  try {
    var channelID = '';
    var emoji = '';
    var authorId = '';
    if (reaction.partial) {
      console.log('REMOVE partial!');
      reaction
        .fetch()
        .then((fullReaction) => {
          channelID = fullReaction.message.channel.id;
          emoji = fullReaction.emoji.name;
          authorId = fullReaction.message.author.id;

          // if channel is posting channel
          if (channelID == smugboardID) {
            logger.error('Reaction is in rashers channel');
            return;
          }
          // if reaction is not desired emoji
          if (emoji !== settings.reactionEmoji) {
            return;
          }
          //no self reacts count
          console.log(user.id + ' ' + authorId);
          if (
            user.id == authorId &&
            user.id != process.env.BYPASS_CHECKS_USER_ID
          ) {
            logger.error('Self reacts do not count');
            return;
          }

          reaction
            .fetch()
            .then((fullReaction) => {
              messageReactionRemoveHelper(fullReaction);
            })
            .catch((error) => {
              console.log(
                'Something went wrong when fetching the message: ',
                error
              );
            });
        })
        .catch((error) => {
          console.log(
            'Something went wrong when fetching the message: ',
            error
          );
        });
    } else {
      channelID = reaction.message.channel.id;
      emoji = reaction.emoji.name;
      authorId = reaction.message.author.id;
    }
    // if channel is posting channel
    if (channelID == smugboardID) {
      logger.error('Reaction is in rashers channel');
      return;
    }
    // if reaction is not desired emoji
    if (emoji !== settings.reactionEmoji) {
      return;
    }
    //no self reacts count
    if (user.id == authorId && user.id != process.env.BYPASS_CHECKS_USER_ID) {
      logger.error('Self reacts do not count');
      return;
    } else messageReactionRemoveHelper(reaction);
  } catch (e) {
    logger.error(e.message);
  }
});

function updateRashersBoard(reaction, reactionCount) {
  MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
    if (err) throw err;
    var dbo = db.db(databaseName);
    var collectionName = process.env.GREGG_RASHERS_BOARD_POSTS_COLLECTION;
    if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
    dbo.collection(collectionName).findOneAndUpdate(
      {
        msgId: reaction.message.id,
        serverID: reaction.message.guild.id,
      },

      {
        $set: {
          reactionCount: reactionCount,
          userID: reaction.message.author.id,
          username: reaction.message.author.username,
        },
        $setOnInsert: {
          entryDate: utils.getCurrentDateTime(),
        },
      },
      { upsert: true, returnDocument: 'after' },
      function (err, res) {
        if (err) throw err;
        var rasherBoardObj = res.value;
        sendLogMessage(
          reaction.message.author.username +
            ' now has a entry in rashersboard collection with count of : ' +
            rasherBoardObj.reactionCount +
            ' rashers'
        );
        if (
          reaction.count < settings.threshold &&
          rasherBoardObj.rasherBoardMsgId
        )
          deletePost(reaction, rasherBoardObj.rasherBoardMsgId);
        else manageBoard(reaction, rasherBoardObj);
        db.close();
        return;
      }
    );
  });
}

function manageBoard(reaction, rasherBoardObj) {
  const msg = reaction.message;
  const postChannel = rashersClient.guilds.cache
    .get(guildID)
    .channels.cache.get(smugboardID);

  // if message is older than set amount
  const dateDiff = new Date() - msg.createdAt;
  const dateCutoff = 1000 * 60 * 60 * 24;
  if (Math.floor(dateDiff / dateCutoff) >= settings.dateCutoff) {
    logger.info(
      `a message older than ${settings.dateCutoff} days was reacted to, ignoring`
    );
    return;
  }

  // did message reach threshold
  if (reaction.count >= settings.threshold) {
    // if message is already posted
    if (rasherBoardObj.rasherBoardMsgId) {
      const editableMessageID = rasherBoardObj.rasherBoardMsgId;
      if (editableMessageID === true) return; // message not yet posted (too fast)
      rashersClient.channels.cache
        .get(process.env.LOGS_CHANNEL_ID)
        .send(
          `updating count of message with ID ${editableMessageID}. reaction count: ${reaction.count}`
        );
      logger.info(
        `updating count of message with ID ${editableMessageID}. reaction count: ${reaction.count}`
      );
      const messageFooter = `${reaction.count} ${settings.embedEmoji} (${msg.id})`;
      postChannel.messages
        .fetch(editableMessageID)
        .then((message) => {
          message.embeds[0].setFooter(messageFooter);
          message.edit({ embeds: [message.embeds[0]] });
        })
        .catch((err) => {
          logger.info(
            `error updating post: ${editableMessageID}\noriginal message: ${msg.id}\n${err}`
          );
        });
    } else {
      rashersClient.channels.cache
        .get(process.env.LOGS_CHANNEL_ID)
        .send(
          `posting message with content ID ${msg.id}. reaction count: ${reaction.count}`
        );
      logger.info(
        `posting message with content ID ${msg.id}. reaction count: ${reaction.count}`
      );

      // create content data
      const data = {
        content:
          msg.content.length < 3920
            ? msg.content
            : `${msg.content.substring(0, 3920)} **[ ... ]**`,
        avatarURL: `https://cdn.discordapp.com/avatars/${msg.author.id}/${msg.author.avatar}.jpg`,
        imageURL: '',
        footer: `${reaction.count} ${settings.embedEmoji} (${msg.id})`,
      };

      // add msg origin info to content prop
      const msgLink = `https://discordapp.com/channels/${msg.guild.id}/${msg.channel.id}/${msg.id}`;
      const channelLink = msg.channel.type.includes('THREAD')
        ? `<#${msg.channel.parent.id}>/<#${msg.channel.id}>`
        : `<#${msg.channel.id}>`;
      data.content += `\n\n→ [original message](${msgLink}) in ${channelLink}`;

      // resolve any images
      if (msg.embeds.length) {
        const imgs = msg.embeds
          .filter((embed) => embed.thumbnail || embed.image)
          .map((embed) =>
            embed.thumbnail ? embed.thumbnail.url : embed.image.url
          );
        data.imageURL = imgs[0];

        // twitch clip check
        const videoEmbed = msg.embeds.filter(
          (embed) => embed.type === 'video'
        )[0];
        if (videoEmbed && videoEmbed.video.url.includes('clips.twitch.tv')) {
          data.content += `\n⬇️ [download clip](${videoEmbed.thumbnail.url.replace(
            '-social-preview.jpg',
            '.mp4'
          )})`;
        }
      } else if (msg.attachments.size) {
        data.imageURL = msg.attachments.first().url;
        data.content += `\n📎 [${msg.attachments.first().name}](${
          msg.attachments.first().proxyURL
        })`;
      }

      const embed = new Discord.MessageEmbed()
        .setAuthor(msg.author.username, data.avatarURL)
        .setColor(settings.hexcolor)
        .setDescription(data.content)
        .setImage(data.imageURL)
        .setTimestamp(new Date())
        .setFooter(data.footer);
      postChannel.send({ embeds: [embed] }).then((rasherBoardMessage) => {
        MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
          if (err) throw err;
          var dbo = db.db(databaseName);
          var collectionName = process.env.GREGG_RASHERS_BOARD_POSTS_COLLECTION;
          if (!dbo.collection(collectionName))
            dbo.createCollection(collectionName);
          dbo.collection(collectionName).findOneAndUpdate(
            {
              msgId: reaction.message.id,
              serverID: reaction.message.guild.id,
            },
            {
              $set: {
                rasherBoardMsgId: rasherBoardMessage.id,
              },
            },
            { upsert: true, returnDocument: 'after' },
            function (err, res) {
              if (err) throw err;
              var rasherObj = res.value;
              logger.info(rasherObj.reactionCount);
              sendLogMessage(
                reaction.message.author.username +
                  ' now has a entry in rashersboard collection with count of : ' +
                  rasherObj.count +
                  ' rashers and boardmsgId of: ' +
                  rasherBoardMessage
              );
              db.close();
              return;
            }
          );
        });
      });
    }
  }
}
function deletePost(reaction, rasherBoardMsgId) {
  const postChannel = rashersClient.guilds.cache
    .get(guildID)
    .channels.cache.get(smugboardID);
  // if posted to channel board before
  postChannel.messages.fetch(rasherBoardMsgId).then((message) => {
    message.delete();
    MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
      if (err) throw err;
      var dbo = db.db(databaseName);
      var collectionName = process.env.GREGG_RASHERS_BOARD_POSTS_COLLECTION;
      if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
      dbo.collection(collectionName).updateOne(
        {
          msgId: reaction.message.id,
          serverID: reaction.message.guild.id,
        },
        {
          $unset: {
            rasherBoardMsgId: '',
          },
        },
        { upsert: false, returnDocument: 'after' },
        function (err, res) {
          if (err) throw err;

          db.close();
        }
      );
    });
  });
}
// // ON REACTION PURGE
// client.on('messageReactionRemoveAll', (msg) => {
//   try {
//     deletePost(msg);
//   } catch (e) {}
// });

// // if post is deleted (rashersdb only)
// client.on('messageDelete', (msg) => {
//   try {
//     if (rashersdb && msg.channel.id === smugboardID)
//       rashersdb.setDeleted(msg.id);
//   } catch (e) {}
// });

// // if embed was deleted (rashersdb only)
// client.on('messageUpdate', (oldMsg, newMsg) => {
//   try {
//     if (
//       rashersdb &&
//       oldMsg.channel.id === smugboardID &&
//       oldMsg.embeds.length &&
//       !newMsg.embeds.length
//     )
//       rashersdb.setDeleted(newMsg.id);
//   } catch (e) {}
// });

function reactionDateCutoff(reaction) {
  // if message is older than set amount
  const dateDiff = new Date() - reaction.message.createdAt;
  const dateCutoff = 1000 * 60 * 60 * 24;
  if (Math.floor(dateDiff / dateCutoff) >= settings.dateCutoff) {
    logger.info(
      `a message older than ${settings.dateCutoff} days was reacted to, ignoring`
    );
    return;
  }
}

function getAllRasherMsgIds() {
  MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
    if (err) throw err;
    var dbo = db.db(databaseName);
    var collectionName = process.env.GREGG_RASHERS_MESSAGE_ID_COLLECTION;
    if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
    dbo
      .collection(collectionName)
      .find({})
      .toArray(function (err, result) {
        if (err) throw err;
        for (rashersMsgIdObj of result) {
          rasherMsgIds.add(rashersMsgIdObj.msgId);
        }
        console.log(rasherMsgIds.size);
        db.close();
      });
  });
}
function rasherRank(msg) {
  var findUserId = '';
  var findUsername = '';
  if (msg.mentions.users.first()) {
    findUserId = msg.mentions.users.first().id;
    findUsername = msg.mentions.users.first().username;
  } else {
    findUserId = msg.author.id;
    findUsername = msg.author.username;
  }
  console.log(findUserId);
  MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
    if (err) throw err;
    var dbo = db.db(databaseName);
    var collectionName = process.env.GREGG_RASHERS_COLLECTION;
    if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
    dbo
      .collection(collectionName)
      .find()
      .sort({ count: -1 })
      .toArray(function (err, result) {
        if (err) throw err;
        try {
          for (let i = 0; i < result.length; i++) {
            if (result[i].userID === findUserId) {
              getPreviousRashersForRank(
                msg,
                findUsername,
                result[i].count,
                i + 1,
                findUserId
              );
              return;
            }
          }
          messageHelper.deleteMsg(msg);
          console.log(findUsername);
          messageHelper.sendNoRashersCurrentlyMessage(msg, findUsername);
        } catch (e) {
          logger.error('Error here: ' + e.message);
        }
      });
  });
}

function getPreviousRashersForRank(
  msg,
  findUsername,
  rashersCount,
  rank,
  findUserId
) {
  MongoClient.connect(process.env.MONGODB_SRV, function (err, db) {
    if (err) throw err;
    var dbo = db.db(databaseName);
    var collectionName = process.env.GREGG_RASHERS_BOARD_POSTS_COLLECTION;
    if (!dbo.collection(collectionName)) dbo.createCollection(collectionName);
    dbo
      .collection(collectionName)
      .find({ userID: findUserId, reactionCount: { $gte: settings.threshold } })
      .sort({ reactionCount: -1, entryDate: -1 })
      .toArray(function (err, result) {
        if (err) throw err;
        try {
          if (result.length == 0) {
            messageHelper.sendRasherRankEmbedMessage(
              msg,
              findUsername,
              rashersCount,
              rank,
              result
            );
          } else {
            messageHelper.sendRasherRankWithRasherBoardsEmbedMessage(
              msg,
              findUsername,
              rashersCount,
              rank,
              result
            );
          }
          messageHelper.deleteMsg(msg);
        } catch (e) {
          logger.error('Error here: ' + e.message);
        }
      });
  });
}

rashersClient.on('messageCreate', (msg) => {
  if (
    msg.content.startsWith(process.env.RASHERS_RANK_COMMAND) &&
    msg.member.permissions.has(process.env.ADMIN_PERMISSION)
  )
    rasherRank(msg);
});

function sendLogMessage(msg) {
  rashersClient.channels.cache.get(process.env.LOGS_CHANNEL_ID).send(msg);
}
