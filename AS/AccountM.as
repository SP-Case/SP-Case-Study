//11 axioms
package AccountM;
import Account;
import Rate;
{

Spec AccountM;
	uses Account,UtilOp,Rate,Account,Integer,RID,Limit,RDB,UserDB,WDReturn;
	Tran
		withdraw(Integer,Integer,Integer,RID,Limit,RDB,UserDB):WDReturn;	//userid, time, amount
	Axiom
		For all am:AccountM, util:UtilOp, u,t,n:Integer, rid:RID, l:Limit, dbr:RDB, dbu:UserDB that
			let
				re = am.withdraw(u,t,n,rid,l,dbr,dbu)
				ou = util.getDataById(u,dbu)
			in
				re.rre.rec.time = t, if re.status = true;
				re.ure.user.balance = ou.balance - n, if re.status = true, ou.balance >= n;
				re.ure.user = null, if re.status = true, ou.balance >= n;
			End
		End

		For am:AccountM, a:Account, u,t1,t2,n:Integer, rid:RID, l:Limit, dbr:RDB, dbu:UserDB that
			let
				u1 = a.getBalance(u,dbu)
				re1 = am.withdraw(u,t1,n,rid,l,dbr,dbu)
				u2 = a.getBalance(u,re1.ure.udb)
				re2 = am.withdraw(u,t2,n,rid,l,re1.rre.rdb,re1.ure.udb)
			in
				re1.status = true, if dbr.datas = nil;
				re2.status = false, if dbr.datas = nil, t2 - t1 < l.dur;
				re2.ure.user = null, if dbr.datas = nil, t2 - t1 < l.dur;
				re2.status = true, if dbr.datas = nil, t2 - t1 >= l.dur;
				u2.balance = u1.balance - n, if re1.status = true, u1.balance >= n;
				u2.balance = u1.balance, if u1.balance < n;
				re2.ure.user.balance = u2.balance - n, if re1.status = true, re2.status = true, u1.balance >= n + n;
				re2.ure.user = null, if re1.status = true, u1.balance >= n + n;
			End
		End
End
}