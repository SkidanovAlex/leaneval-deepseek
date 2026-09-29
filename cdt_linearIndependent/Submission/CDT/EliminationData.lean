import Mathlib

/-!
# The explicit coefficients of the eliminated operator of CDT Lemma `14functions`

The second half of the paper's Lemma `14functions` eliminates `b0,b1,b2` from the
system
```
b3' + b2 - (c3/c4) b3 = 0,   b2' + b1 - (c2/c4) b3 = 0,
b1' + b0 - (c1/c4) b3 = 0,   b0'      - (c0/c4) b3 = R
```
and obtains `\sum_{j=0}^4 Q_j b3^{(j)} = R` with `Q_4 = -1`,
`Q_j = 2 P_j / D1^(4-j)` for `j <= 3`, where `D1 = y(y-4)(72y+1)(144y^3-122y^2+118y-1)`.
The four identities below are the coefficient-wise statement of
`D[(c1/c4) f] - D^2[(c2/c4) f] + D^3[(c3/c4) f] - (c0/c4) f - f'''' = \sum_j Q_j f^{(j)}`
(i.e. the coefficients of `f, f', f'', f'''`), verified by `ring`.
-/

noncomputable section

namespace Submission.CDT.Elim14

abbrev y : Polynomial ℚ := Polynomial.X
/-- `c0` -/
def c0 : Polynomial ℚ :=
  ((-54:ℤ) : Polynomial ℚ) + ((-2268:ℤ) : Polynomial ℚ) * y + ((12816:ℤ) : Polynomial ℚ) * y^2 + ((-6480:ℤ) : Polynomial ℚ) * y^3
/-- `c1` -/
def c1 : Polynomial ℚ :=
  ((-4:ℤ) : Polynomial ℚ) + ((-5522:ℤ) : Polynomial ℚ) * y + ((283264:ℤ) : Polynomial ℚ) * y^2 + ((-560656:ℤ) : Polynomial ℚ) * y^3 + ((352824:ℤ) : Polynomial ℚ) * y^4 + ((-191232:ℤ) : Polynomial ℚ) * y^5 + ((41472:ℤ) : Polynomial ℚ) * y^6
/-- `c2` -/
def c2 : Polynomial ℚ :=
  ((-68:ℤ) : Polynomial ℚ) * y + ((-12706:ℤ) : Polynomial ℚ) * y^2 + ((1380710:ℤ) : Polynomial ℚ) * y^3 + ((-2131226:ℤ) : Polynomial ℚ) * y^4 + ((1735752:ℤ) : Polynomial ℚ) * y^5 + ((-876672:ℤ) : Polynomial ℚ) * y^6 + ((145152:ℤ) : Polynomial ℚ) * y^7
/-- `c3` -/
def c3 : Polynomial ℚ :=
  ((-80:ℤ) : Polynomial ℚ) * y^2 + ((-1612:ℤ) : Polynomial ℚ) * y^3 + ((945968:ℤ) : Polynomial ℚ) * y^4 + ((-1411958:ℤ) : Polynomial ℚ) * y^5 + ((1436676:ℤ) : Polynomial ℚ) * y^6 + ((-617472:ℤ) : Polynomial ℚ) * y^7 + ((82944:ℤ) : Polynomial ℚ) * y^8
/-- `c4` -/
def c4 : Polynomial ℚ :=
  ((-16:ℤ) : Polynomial ℚ) * y^3 + ((744:ℤ) : Polynomial ℚ) * y^4 + ((133615:ℤ) : Polynomial ℚ) * y^5 + ((-205186:ℤ) : Polynomial ℚ) * y^6 + ((243382:ℤ) : Polynomial ℚ) * y^7 + ((-91584:ℤ) : Polynomial ℚ) * y^8 + ((10368:ℤ) : Polynomial ℚ) * y^9
/-- `cub` -/
def cub : Polynomial ℚ :=
  ((-1:ℤ) : Polynomial ℚ) + ((118:ℤ) : Polynomial ℚ) * y + ((-122:ℤ) : Polynomial ℚ) * y^2 + ((144:ℤ) : Polynomial ℚ) * y^3
/-- `D1` -/
def D1 : Polynomial ℚ :=
  ((4:ℤ) : Polynomial ℚ) * y + ((-185:ℤ) : Polynomial ℚ) * y^2 + ((-33450:ℤ) : Polynomial ℚ) * y^3 + ((42934:ℤ) : Polynomial ℚ) * y^4 + ((-50112:ℤ) : Polynomial ℚ) * y^5 + ((10368:ℤ) : Polynomial ℚ) * y^6
/-- `P0` -/
def P0 : Polynomial ℚ :=
  ((-7200:ℤ) : Polynomial ℚ) + ((986352:ℤ) : Polynomial ℚ) * y + ((212214654:ℤ) : Polynomial ℚ) * y^2 + ((-23725872555:ℤ) : Polynomial ℚ) * y^3 + ((-2926882304952:ℤ) : Polynomial ℚ) * y^4 + ((216737101843912:ℤ) : Polynomial ℚ) * y^5 + ((23909744619189904:ℤ) : Polynomial ℚ) * y^6 + ((441147318433673076:ℤ) : Polynomial ℚ) * y^7 + ((-72492936767952071328:ℤ) : Polynomial ℚ) * y^8 + ((368523624159632786864:ℤ) : Polynomial ℚ) * y^9 + ((-1130163040657708666464:ℤ) : Polynomial ℚ) * y^10 + ((2321090076590185198688:ℤ) : Polynomial ℚ) * y^11 + ((-3561389436827812851072:ℤ) : Polynomial ℚ) * y^12 + ((4138978906343379271680:ℤ) : Polynomial ℚ) * y^13 + ((-3685977058095537647616:ℤ) : Polynomial ℚ) * y^14 + ((2389193597708690522112:ℤ) : Polynomial ℚ) * y^15 + ((-1108518733194486349824:ℤ) : Polynomial ℚ) * y^16 + ((364052253723649376256:ℤ) : Polynomial ℚ) * y^17 + ((-81465669759377866752:ℤ) : Polynomial ℚ) * y^18 + ((11442281356059475968:ℤ) : Polynomial ℚ) * y^19 + ((-831979165027663872:ℤ) : Polynomial ℚ) * y^20
/-- `P1` -/
def P1 : Polynomial ℚ :=
  ((1512:ℤ) : Polynomial ℚ) + ((-134902:ℤ) : Polynomial ℚ) * y + ((-38589099:ℤ) : Polynomial ℚ) * y^2 + ((2104243236:ℤ) : Polynomial ℚ) * y^3 + ((410207848954:ℤ) : Polynomial ℚ) * y^4 + ((7908910476968:ℤ) : Polynomial ℚ) * y^5 + ((-1646469966968208:ℤ) : Polynomial ℚ) * y^6 + ((6316493599080888:ℤ) : Polynomial ℚ) * y^7 + ((-15346937682258608:ℤ) : Polynomial ℚ) * y^8 + ((23626972684795104:ℤ) : Polynomial ℚ) * y^9 + ((-26419367464851456:ℤ) : Polynomial ℚ) * y^10 + ((19378210822907904:ℤ) : Polynomial ℚ) * y^11 + ((-9654120171307008:ℤ) : Polynomial ℚ) * y^12 + ((3169490107170816:ℤ) : Polynomial ℚ) * y^13 + ((-621031163166720:ℤ) : Polynomial ℚ) * y^14 + ((60183678025728:ℤ) : Polynomial ℚ) * y^15
/-- `P2` -/
def P2 : Polynomial ℚ :=
  ((-154:ℤ) : Polynomial ℚ) + ((6311:ℤ) : Polynomial ℚ) * y + ((2972689:ℤ) : Polynomial ℚ) * y^2 + ((59401743:ℤ) : Polynomial ℚ) * y^3 + ((-17804559936:ℤ) : Polynomial ℚ) * y^4 + ((45642482386:ℤ) : Polynomial ℚ) * y^5 + ((-81611663964:ℤ) : Polynomial ℚ) * y^6 + ((72778477824:ℤ) : Polynomial ℚ) * y^7 + ((-43238458368:ℤ) : Polynomial ℚ) * y^8 + ((14058012672:ℤ) : Polynomial ℚ) * y^9 + ((-2042413056:ℤ) : Polynomial ℚ) * y^10
/-- `P3` -/
def P3 : Polynomial ℚ :=
  ((10:ℤ) : Polynomial ℚ) + ((204:ℤ) : Polynomial ℚ) * y + ((-118195:ℤ) : Polynomial ℚ) * y^2 + ((146946:ℤ) : Polynomial ℚ) * y^3 + ((-142848:ℤ) : Polynomial ℚ) * y^4 + ((41472:ℤ) : Polynomial ℚ) * y^5
/-- `c1d` -/
def c1d : Polynomial ℚ :=
  ((-5522:ℤ) : Polynomial ℚ) + ((566528:ℤ) : Polynomial ℚ) * y + ((-1681968:ℤ) : Polynomial ℚ) * y^2 + ((1411296:ℤ) : Polynomial ℚ) * y^3 + ((-956160:ℤ) : Polynomial ℚ) * y^4 + ((248832:ℤ) : Polynomial ℚ) * y^5
/-- `c2d` -/
def c2d : Polynomial ℚ :=
  ((-68:ℤ) : Polynomial ℚ) + ((-25412:ℤ) : Polynomial ℚ) * y + ((4142130:ℤ) : Polynomial ℚ) * y^2 + ((-8524904:ℤ) : Polynomial ℚ) * y^3 + ((8678760:ℤ) : Polynomial ℚ) * y^4 + ((-5260032:ℤ) : Polynomial ℚ) * y^5 + ((1016064:ℤ) : Polynomial ℚ) * y^6
/-- `c2dd` -/
def c2dd : Polynomial ℚ :=
  ((-25412:ℤ) : Polynomial ℚ) + ((8284260:ℤ) : Polynomial ℚ) * y + ((-25574712:ℤ) : Polynomial ℚ) * y^2 + ((34715040:ℤ) : Polynomial ℚ) * y^3 + ((-26300160:ℤ) : Polynomial ℚ) * y^4 + ((6096384:ℤ) : Polynomial ℚ) * y^5
/-- `c3d` -/
def c3d : Polynomial ℚ :=
  ((-160:ℤ) : Polynomial ℚ) * y + ((-4836:ℤ) : Polynomial ℚ) * y^2 + ((3783872:ℤ) : Polynomial ℚ) * y^3 + ((-7059790:ℤ) : Polynomial ℚ) * y^4 + ((8620056:ℤ) : Polynomial ℚ) * y^5 + ((-4322304:ℤ) : Polynomial ℚ) * y^6 + ((663552:ℤ) : Polynomial ℚ) * y^7
/-- `c3dd` -/
def c3dd : Polynomial ℚ :=
  ((-160:ℤ) : Polynomial ℚ) + ((-9672:ℤ) : Polynomial ℚ) * y + ((11351616:ℤ) : Polynomial ℚ) * y^2 + ((-28239160:ℤ) : Polynomial ℚ) * y^3 + ((43100280:ℤ) : Polynomial ℚ) * y^4 + ((-25933824:ℤ) : Polynomial ℚ) * y^5 + ((4644864:ℤ) : Polynomial ℚ) * y^6
/-- `c3ddd` -/
def c3ddd : Polynomial ℚ :=
  ((-9672:ℤ) : Polynomial ℚ) + ((22703232:ℤ) : Polynomial ℚ) * y + ((-84717480:ℤ) : Polynomial ℚ) * y^2 + ((172401120:ℤ) : Polynomial ℚ) * y^3 + ((-129669120:ℤ) : Polynomial ℚ) * y^4 + ((27869184:ℤ) : Polynomial ℚ) * y^5
/-- `c4d` -/
def c4d : Polynomial ℚ :=
  ((-48:ℤ) : Polynomial ℚ) * y^2 + ((2976:ℤ) : Polynomial ℚ) * y^3 + ((668075:ℤ) : Polynomial ℚ) * y^4 + ((-1231116:ℤ) : Polynomial ℚ) * y^5 + ((1703674:ℤ) : Polynomial ℚ) * y^6 + ((-732672:ℤ) : Polynomial ℚ) * y^7 + ((93312:ℤ) : Polynomial ℚ) * y^8
/-- `c4dd` -/
def c4dd : Polynomial ℚ :=
  ((-96:ℤ) : Polynomial ℚ) * y + ((8928:ℤ) : Polynomial ℚ) * y^2 + ((2672300:ℤ) : Polynomial ℚ) * y^3 + ((-6155580:ℤ) : Polynomial ℚ) * y^4 + ((10222044:ℤ) : Polynomial ℚ) * y^5 + ((-5128704:ℤ) : Polynomial ℚ) * y^6 + ((746496:ℤ) : Polynomial ℚ) * y^7
/-- `c4ddd` -/
def c4ddd : Polynomial ℚ :=
  ((-96:ℤ) : Polynomial ℚ) + ((17856:ℤ) : Polynomial ℚ) * y + ((8016900:ℤ) : Polynomial ℚ) * y^2 + ((-24622320:ℤ) : Polynomial ℚ) * y^3 + ((51110220:ℤ) : Polynomial ℚ) * y^4 + ((-30772224:ℤ) : Polynomial ℚ) * y^5 + ((5225472:ℤ) : Polynomial ℚ) * y^6

/-- identity (1): the coefficient of `f'''`. -/
theorem coeff_ident_three : 2 * P3 * c4 = c3 * D1 := by
  unfold P3 c4 c3 D1 y; ring

/-- identity (2): the coefficient of `f''`. -/
theorem coeff_ident_two : (-c2*c4 + 3*(c3d*c4 - c3*c4d))*D1^2 = 2*P2*c4^2 := by
  unfold P2 c2 c3 c4 c3d c4d D1 y; ring

/-- identity (3): the coefficient of `f'`. -/
theorem coeff_ident_one : (c1*c4^2 - 2*(c2d*c4 - c2*c4d)*c4 + 3*(c3dd*c4^2 - 2*c3d*c4*c4d - c3*c4dd*c4 + 2*c3*c4d^2))*D1^3 = 2*P1*c4^3 := by
  unfold P1 c1 c2 c3 c4 c2d c3d c3dd c4d c4dd D1 y; ring

/-- identity (4): the coefficient of `f`. -/
theorem coeff_ident_zero : ((c1d*c4 - c1*c4d)*c4^2
           - (c2dd*c4^2 - 2*c2d*c4*c4d - c2*c4dd*c4 + 2*c2*c4d^2)*c4
           + (c3ddd*c4^3 - 3*c3dd*c4^2*c4d + 3*c3d*(2*c4d^2 - c4*c4dd)*c4
              - c3*(6*c4d^3 - 6*c4*c4d*c4dd + c4^2*c4ddd))
           - c0*c4^3)*D1^4 = 2*P0*c4^4 := by
  unfold P0 c0 c1 c2 c3 c4 c1d c2d c2dd c3d c3dd c3ddd c4d c4dd c4ddd D1 y; ring

end Submission.CDT.Elim14
