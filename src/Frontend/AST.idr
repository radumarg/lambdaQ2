module Frontend.AST

import Derive.Prelude
import Language.Reflection

%default total
%language ElabReflection

public export
data GateName
  = GateId | GateX | GateY | GateZ | GateH
  | GateS | GateSDG | GateT | GateTDG
  | GateSX | GateSXDG
  | GateRX | GateRY | GateRZ
  | GateU1 | GateU2 | GateU3
  | GateCNOT | GateCX                                           -- allow both spellings;
  | GateCY | GateCZ | GateCS | GateCSDG | GateCT | GateCTDG
  | GateCSX | GateCSXDG
  | GateCRX | GateCRY | GateCRZ
  | GateCU1 | GateCU2 | GateCU3
  | GateSWAP
  | GateRXX | GateRYY | GateRZZ
  | GateCCX | GateCSWAP
  | GateGPI | GateGPI2 | GateMS

%runElab derive "GateName" [Show,Eq]