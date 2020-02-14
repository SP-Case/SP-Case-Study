//6 axioms
package AccountMImp;
import Account;
import Rate;
{

Spec WDReturn;
	uses Bool,UserReturn,RReturn;
	Attr
		status:Bool;
		ure:UserReturn;
		rre:RReturn;
End

Spec AccountM;
	uses UtilOp,Rate,Account,Integer,RID,Limit,RDB,UserDB,WDReturn;
	Tran
		withdraw(Integer,Integer,Integer,RID,Limit,RDB,UserDB):WDReturn;	//userid, time, amount
	Axiom
		For all am:AccountM, r:Rate, a:Account, u,t,n:Integer, rid:RID, l:Limit, dbr:RDB, dbu:UserDB that
			let re = am.withdraw(u,t,n,rid,l,dbr,dbu) in
				re.status = r.checkRate(u,t,rid,WD,l,db);
				re.rre = r.refreshTime(rid,t,dbr), if re.status = true;
				re.ure = a.subBalance(u,n,dbu), if re.status = true;
				re.ure.user = null, if re.status = false;
				re.ure.udb = dbu, if re.status = false;
				re.rre.rdb = dbr, if re.status = false;
			End
		End
End
}