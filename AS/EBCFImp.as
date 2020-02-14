//25 axioms
package EBCFImp;
import Log;
import Stop;
import AccountM;
import DonateM;
{

Spec RCReturn;
extends ReturnWithLog;
	uses UserReturn;
	Attr
		ure:UserReturn;
End

Spec WDLReturn;
extends ReturnWithLog;
	uses WDReturn;
	Attr
		wre:WDReturn;
End

Spec SPLReturn;
extends ReturnWithLog;
	uses EUReturn;
	Attr
		eure:EUReturn;
End

Spec DLReturn;
extends ReturnWithLog;
	uses DEReturn;
	Attr
		dere:DEReturn;
End

Spec EBCF;
	uses Log,AccountM,Donate,Integer,RID,Limit,RDB,UserDB,LogDB,EventDB,
		DonateDB,Status,RCReturn,WDLReturn,SPLReturn,DLReturn;
	Tran
		rechargeWithLog(Integer,Integer,UserDB,LogDB,Status):RCReturn;
		withdrawWithLog(Integer,Integer,Integer,RID,Limit,RDB,UserDB,LogDB):WDLReturn;
		stopAndPayWithLog(Integer,Integer,EventDB,UserDB,LogDB,Status):SPLReturn;
		donateWithLog(Integer,Integer,Integer,DonateDB,EventDB,UserDB,LogDB):DLReturn;
	Axiom
		For all ebcf:EBCF, l:Log, am:AccountM, u,n:Integer, dbu:UserDB, dbl:LogDB, s:Status that
			let re = ebcf.rechargeWithLog(u,n,dbu,dbl,s) in 
				re.ure = am.addBalance(u,n,dbu), if s.value = true;
				re.lre = l.log(u,RC,dbl), if s.value = true;

				re.ure.user = null, if s.value = false;
				re.ure.udb = dbu, if s.value = false;
				re.lre.ldb = dbl, if s.value = false;
			End
		End

		For all ebcf:EBCF, l:Log, am:AccountM, u,t,n:Integer, rid:RID, l:Limit, dbr:RDB, 
				dbu:UserDB, dbl:LogDB, s:Status that
			let re = ebcf.withdrawWithLog(u,t,n,rid,l,dbr,dbu,dbl,s) in 
				re.wre = am.withdraw(u,t,n,rid,l,dbr,dbu), if s.value = true;
				re.lre = l.log(u,WD,dbl), if s.value = true;

				re.wre.ure.user = null, if s.value = false;	
				re.wre.ure.udb = dbu, if s.value = false;
				re.lre.ldb = dbl, if s.value = false;
				re.wre.rre.rdb = dbr, if s.value = false;
			End
		End

		For all ebcf:EBCF, l:Log, em:EventM, u,i:Integer, dbe:EventDB, dbu:UserDB, dbl:LogDB, s:Status that
			let re = ebcf.stopAndPayWithLog(u,i,dbe,dbu,dbl,s) in 
				re.eure = em.stopAndPay(u,i,dbe,dbu), if s.value = true;
				re.lre = l.log(u,SE,dbl), if s.value = true;

				re.eure.ure.user = null, if s.value = false;	
				re.eure.ere.e = null, if s.value = false;	
				re.eure.ure.udb = dbu, if s.value = false;	
				re.eure.ere.edb = dbe, if s.value = false;	
				re.lre.ldb = dbl, if s.value = false;	
			End
		End

		For all ebcf:EBCF, l:Log, dm:DonateM, ui,ei,n:Integer, dbd:DonateDB, 
				dbe:EventDB, dbu:UserDB, dbl:LogDB, s:Status that
			let re = ebcf.donateWithLog(ui,ei,n,dbd,dbe,dbu,dbl,s) in 
				re.dere = dm.donate(ui,ei,n,dbd,dbe,dbu), if s.value = true;
				re.lre = l.log(u,DN,dbl), if s.value = true;

				re.dere.dre.d = null, if s.value = false;
				re.dere.ere.e = null, if s.value = false;
				re.dere.ure.udb = dbu, if s.value = false;
				re.dere.ere.edb = dbe, if s.value = false;
				re.lre.ldb = dbl, if s.value = false;
			End
		End
End
}