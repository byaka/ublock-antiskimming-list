# -*- coding: utf-8 -*-
import sys, os, re, time
sys.path.append('libs/')

from functionsex import *

class updater(object):

   def __init__(self, path=None, gitcmd=None):
      self._path=path or '/'.join(getScriptPath().split('/')[:-1])
      self._gitcmd=gitcmd or 'git'
      try:
         cmd((self._gitcmd, 'status'), path=self._path)
      except Exception, e:
         raise ValueError('Cant call git "%s": %s'%(self._gitcmd, e))
      self._sourcePath=self._path+'/source/'
      self._outputPath=self._path+'/build/'
      self._dataPath=self._sourcePath+'data.txt'
      self._infoPath=self._sourcePath+'info.txt'
      for s in (self._path, self._sourcePath, self._outputPath, self._dataPath, self._infoPath):
         if not os.path.exists(s):
            raise ValueError('Path not exist: "%s"'%s)
      self._needStop=False
      self._timeSleep=60
      self._interval=3*60*60
      self._lastRun=None
      self._lastChange=None
      self._re_builder=(r'^(.+)$', r'||\1^$document')
      self._url=['https://gitlab.com/gwillem/public-snippets/snippets/28813/raw']

   def __call__(self):
      self.start()

   def download(self):
      for url in self._url:
         data=getHtml2(url, followRedirect=True, headers={}, type='get', timeout=180, returnOnlyData=True)
         if not data: continue
         return data
      return None

   def gitCommit(self):
      r=cmd((self._gitcmd, 'add', '.'), path=self._path)
      print '>> [add]', r, raw_input()
      r=cmd((self._gitcmd, 'commit', '-m', 'Auto-updating'), path=self._path)
      print '>> [commit]', r, raw_input()
      r=cmd((self._gitcmd, 'push', 'origin', 'master'), path=self._path)
      print '>> [push]', r, raw_input()

   def stop(self):
      self._needStop=True

   def start(self):
      print 'Main cicle started!'
      while not self._needStop:
         if not self._lastRun or getms(False)-self._lastRun>=self._interval:
            try:
               data=self.download()
               if data:
                  data=data.replace('\r', '')
                  hashNew=sha256(data.strip())
                  hashOld=sha256(fileGet(self._dataPath).replace('\r', '').strip())
                  print '~', hashOld!=hashNew
                  if hashOld!=hashNew:
                     d=datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S')
                     print 'New changes founded..', d
                     if not data.endswith('\n'): data+='\n'
                     dataBuilded=re.sub(self._re_builder[0], self._re_builder[1], data, flags=re.MULTILINE)
                     dataBuilded='%s\n! Updated: %s\n\n%s'%(fileGet(self._infoPath), d, dataBuilded)
                     print '   Updating source..'
                     fileWrite(self._dataPath, data)
                     print '   Updating output..'
                     fileWrite(self._outputPath+'data.txt', dataBuilded)
                     print '   Pushing to git..'
                     self.gitCommit()
                     self._lastChange=getms(False)
                     print '   OK'
               self._lastRun=getms(False)
            except Exception, e:
               print '!!! Some error in main cicle: %s'%e
         time.sleep(self._timeSleep)

if __name__ == '__main__':
   main=updater()
   main()
