//48 axioms
package EBCF;
import Log;
import Stop;
import AccountM;
import DonateM;
{

Spec EBCF;
	uses UtilOp,Log,AccountM,Donate,Integer,RID,Limit,RDB,UserDB,LogDB,EventDB,
		DonateDB,Status,RCReturn,WDLReturn,SPLReturn,DLReturn;
	Tran
		rechargeWithLog(Integer,Integer,UserDB,LogDB,Status):RCReturn;
		withdrawWithLog(Integer,Integer,Integer,RID,Limit,RDB,UserDB,LogDB):WDLReturn;
		stopAndPayWithLog(Integer,Integer,EventDB,UserDB,LogDB,Status):SPLReturn;
		donateWithLog(Integer,Integer,Integer,DonateDB,EventDB,UserDB,LogDB):DLReturn;
	Axiom
		//22 axioms
		For all ebcf:EBCF, util:UtilOp, u,n:Integer, dbu:UserDB, dbl:LogDB, s:Status that
			let 
				re = ebcf.rechargeWithLog(u,n,dbu,dbl,s) 
				ou = util.getDataById(u,dbu)
			in 
				re.ure.user.balance = ou.balance + n, if s.value = true, re.ure.user <> null;
				re.lre.log.uid = u, if s.value = true;
				re.lre.log.op = RC, if s.value = true;
				re.ure.user = null, if s.value = false;
			End
		End

		For all ebcf:EBCF, util:UtilOp, u,t,n:Integer, rid:RID, l:Limit, dbr:RDB, 
				dbu:UserDB, dbl:LogDB, s:Status that
			let 
				re = ebcf.withdrawWithLog(u,t,n,rid,l,dbr,dbu,dbl,s) 
				ou = util.getDataById(u,dbu)
			in 
				re.wre.ure.user.balance = ou.balance - n, if dbr.datas = nil, s.value = true, ou.balance >= n;
				re.wre.ure.user = null, if ou.balance < n;
				re.lre.log.uid = u, if s.value = true;
				re.lre.log.op = WD, if s.value = true;
				re.wre.ure.user = null, if s.value = false;
			End
		End

		For all ebcf:EBCF, util:UtilOp, u,i:Integer, dbe:EventDB, dbu:UserDB, dbl:LogDB, s:Status that
			let 
				re = ebcf.stopAndPayWithLog(u,i,dbe,dbu,dbl,s) 
				ou = util.getDataById(u,dbu)
				ev = util.getDataById(i,dbe)
			in 
				re.eure.ere.e.status = false, if s.value = true, ev.uid = u, ev.status = true;
				re.eure.ure.user.balance = ou.balance + re.eure.ere.e.total, if re.eure.ure.user <> null;
				re.eure.ere.e = null, if ev.status = false;
				re.eure.ere.e = null, if ev.uid <> u;
				re.lre.log.uid = u, if s.value = true;
				re.lre.log.op = SE, if s.value = true;
				re.eure.ere.edb = dbe, if s.value = false;
			End
		End

		For all ebcf:EBCF, util:UtilOp, ui,ei,n:Integer, dbd:DonateDB, 
				dbe:EventDB, dbu:UserDB, dbl:LogDB, s:Status that
			let 
				re = ebcf.donateWithLog(ui,ei,n,dbd,dbe,dbu,dbl,s)
				ou = util.getDataById(u,dbu)
				ev = util.getDataById(i,dbe)
			in 
				re.dere.ere.e.total = ev.total + n, if s.value = true, ou.balance >= n, ev.status = true;
				re.dere.ere.edb = dbe, if ou.balance < n;
				re.dere.ere.e = null, if ev.status = false;
				re.lre.log.uid = ui, if s.value = true;
				re.lre.log.op = DN, if s.value = true;
				re.dere.ere.edb = dbe, if s.value = false;
			End
		End

		//26 axioms
		For all am:AccountM, ebcf:EBCF, u,t,n1,n2:Integer, rid:RID, 
				l:Limit, dbr:RDB, dbu:UserDB, dbl:LogDB, s:Status that
			let 
				u1 = am.getBalance(u,dbu)
				re1 = ebcf.rechargeWithLog(u,n1,dbu,dbl,s)
				u2 = am.getBalance(u,re1.ure.udb)
				re2 = ebcf.withdrawWithLog(u,t,n2,rid,l,dbr,re1.ure.udb,re1.lre.ldb,s) 
				u3 = am.getBalance(u,re2.wre.ure.udb)
			in
				u3.balance = u1.balance, if s.value = false;
				u2.balance = u1.balance + n1, if s.value = true, u1 <> null;
				u3.balance = u1.balance, if s.value = true, u1 <> null, dbr.datas = nil, n1 = n2;
				u3.balance = u2.balance, if s.value = true, dbr.datas = nil, n2 > n1 + n2;
				re1.lre.log.op = RC, if s.value = true;
				re2.lre.log.op = WD, if s.value = true;
			End
		End

		For all am:AccountM, ebcf:EBCF, u,t1,t2,n1,n2:Integer, rid:RID, 
			l:Limit, dbr:RDB, dbu:UserDB, dbl:LogDB, s:Status that
			let
				u1 = am.getBalance(u,dbu)
				re1 = ebcf.withdrawWithLog(u,t1,n1,rid,l,dbr,dbu,dbl,s)
				u2 = am.getBalance(u,re1.wre.ure.udb)
				re2 = ebcf.withdrawWithLog(u,t2,n2,rid,l,re1.wre.rre.rdb,re1.wre.ure.udb,re1.lre.ldb,s)
				u3 = am.getBalance(u,re2.wre.ure.udb)
			in
				u3.balance = u1.balance, if s.value = false;
				u2.balance = u1.balance - n1, if s.value = true, dbr.datas = nil, u1.balance >= n1;
				u3.balance = u2.balance, if s.value = true, dbr.datas = nil, t2-t1 < l.dur;
				u3.balance = u2.balance - n2, if s.value = true, dbr.datas = nil, t2-t1 >= l.dur;
				u3.balance = u2.balance, if s.value = true, dbr.datas = nil, t2-t1 >= l.dur;
				re1.lre.log.op = WD, if s.value = true;
				re2.lre.log.op = WD, if s.value = true;
			End
		End

		For all am:AccountM, em:EventM, ebcf:EBCF, uid1,uid2,uid3,uid4,tar,n:Integer, 
				c:string, s:Status, ev:Event, dbe:EventDB, dbd:DonateDB, dbu:UserDB, dbl:LogDB that
			let
				u1 = am.getBalance(uid1,dbu)
				u2 = am.getBalance(uid2,dbu)
				re1 = em.createEvent(uid1,tar,c,dbe)
				re2 = ebcf.donateWithLog(uid2,re1.id,n,dbd,re1.edb,dbu,dbl,s)
				re3 = ebcf.stopAndPayWithLog(uid4,re1.id,re2.dere.ere.edb,re2.dere.ure.udb,re2.lre.ldb,s)
				ev = em.getEvent(re1.id,re3.eure.ere.edb)
				u3 = am.getBalance(uid3,re3.eure.ure.udb)
			in
				ev.total = n, if s.value = true, u2.balance >= n;
				ev.total = 0, if s.value = true, u2.balance < n;
				ev.status = true, if s.value = true, uid4 <> uid1;
				ev.status = false, if s.value = true, uid4 = uid1;
				u3.balance = u2.balance - n, if s.value = true, u2.balance >= n, uid3 = uid2, uid1 <> uid2;
				u3.balance = u2.balance, if s.value = true, u2.balance < n, uid3 = uid2;
				u3.balance = u1.balance, if s.value = true, u2.balance < n, uid3 = uid1;
				u3.balance = u1.balance + n, if ev.status = false, uid1 <> uid2, uid3 = uid1;
				re3.lre.log.op = SE, if s.value = true;
			End
		End

		For all am:AccountM, es:EStop, ebcf:EBCF, u,n:Integer, dbu:UserDB, dbl:LogDB, s1,s2:Status that
			let
				re1 = am.getBalance(u,dbu)
				s2 = es.estop(s1,u)
				re2 = ebcf.rechargeWithLog(u,n,dbu,dbl,s2)
			in
				re2.ure.user.balance = re1.balance + n, if u <> s1.admin, s1.value = true;
				s2.value = false, if u = s1.admin;
				re2.ure.udb = dbu, if u = s1.admin;
				re2.ure.user = null, if u = s1.admin;
			End
		End
End
}