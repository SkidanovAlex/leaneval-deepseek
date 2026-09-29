import Mathlib
import Submission.CDT.SympExplicitodeBridge
import Submission.CDT.AintegralAssembled
import Submission.Commons.Analysis.Differential.ode_pullback_involution

/-!
# The paper's eq. `(explicitode)`: `GA_odeLHS = 0`

This module finishes the push-forward proof of the paper's order-4 ODE
(`Scratch/explicitode/README.md`).  The bridge identity
`(x−1)^19·(y′)⁷·(GA_odeLHS ∘ y) = Σ_j Mp_j·F₀⁽ʲ⁾` of
`Submission.CDT.SympExplicitodeBridge` is combined with

* the two second-order ODEs satisfied by the two branches
  `u = H_A` (`HA_ode`, the Franel ODE `a₂u″ + a₁u′ + a₀u = 0`) and
  `v = H_A∘σ` (`Commons.Analysis.Differential.ode_pullback_involution`,
  `N₂v″ + N₁v′ + N₀v = 0`), and
* the ODE *chains* `a₂^k·f^{(k+1)} = r_k·f′ + s_k·f` (and `N₂^k·…` for `v`)
  for `k = 1, 2, 3`, obtained by differentiating the ODE and substituting,

to conclude `Σ_j Mp_j·F₀⁽ʲ⁾ = 0`, hence `(GA_odeLHS)∘y = 0`, hence
`GA_odeLHS = 0` by injectivity of the substitution `y ↦ x²/(x−1)`
(`symp_subst_y_injective`).

All declarations are fully proved (no axioms, no `sorry`).
-/

noncomputable section
open PowerSeries
namespace Submission.CDT

set_option maxRecDepth 10000

/-! ## 0. The formal derivative and its calculus -/

/-- the formal derivative, as a function -/
def Dx (f : PowerSeries ℚ) : PowerSeries ℚ := (PowerSeries.derivative (R := ℚ)) f

lemma Dx_zero : Dx (0 : PowerSeries ℚ) = 0 := by rw [Dx]; exact map_zero _

lemma Dx_one : Dx (1 : PowerSeries ℚ) = 0 := by rw [Dx]; exact PowerSeries.derivative_one

lemma Dx_add (a b : PowerSeries ℚ) : Dx (a + b) = Dx a + Dx b := by
  rw [Dx]; exact map_add _ a b

lemma Dx_sub (a b : PowerSeries ℚ) : Dx (a - b) = Dx a - Dx b := by
  rw [Dx]; exact map_sub _ a b

lemma Dx_mul (a b : PowerSeries ℚ) : Dx (a * b) = a * Dx b + b * Dx a := by
  simp only [Dx, Derivation.leibniz, smul_eq_mul]

lemma Dx_X : Dx (X : PowerSeries ℚ) = 1 := by rw [Dx]; exact derivative_X

lemma Dx_pow (f : PowerSeries ℚ) (n : ℕ) : Dx (f ^ n) = n * f ^ (n - 1) * Dx f := by
  rw [Dx, PowerSeries.derivative_pow]
  rfl

lemma Dx_C_int (z : ℤ) : Dx (PowerSeries.C (z : ℚ)) = 0 := by
  rw [Dx, PowerSeries.derivative_C]

lemma Dx_neg (f : PowerSeries ℚ) : Dx (-f) = -Dx f := by
  rw [Dx]; exact map_neg _ f

lemma Dx_num_2 : Dx (2 : PowerSeries ℚ) = 0 := by
  rw [Dx, show (2 : PowerSeries ℚ) = PowerSeries.C (2 : ℚ) from (map_natCast PowerSeries.C 2).symm, PowerSeries.derivative_C]

lemma Dx_num_3 : Dx (3 : PowerSeries ℚ) = 0 := by
  rw [Dx, show (3 : PowerSeries ℚ) = PowerSeries.C (3 : ℚ) from (map_natCast PowerSeries.C 3).symm, PowerSeries.derivative_C]

lemma Dx_num_4 : Dx (4 : PowerSeries ℚ) = 0 := by
  rw [Dx, show (4 : PowerSeries ℚ) = PowerSeries.C (4 : ℚ) from (map_natCast PowerSeries.C 4).symm, PowerSeries.derivative_C]

lemma Dx_num_5 : Dx (5 : PowerSeries ℚ) = 0 := by
  rw [Dx, show (5 : PowerSeries ℚ) = PowerSeries.C (5 : ℚ) from (map_natCast PowerSeries.C 5).symm, PowerSeries.derivative_C]

lemma Dx_num_6 : Dx (6 : PowerSeries ℚ) = 0 := by
  rw [Dx, show (6 : PowerSeries ℚ) = PowerSeries.C (6 : ℚ) from (map_natCast PowerSeries.C 6).symm, PowerSeries.derivative_C]

lemma Dx_num_8 : Dx (8 : PowerSeries ℚ) = 0 := by
  rw [Dx, show (8 : PowerSeries ℚ) = PowerSeries.C (8 : ℚ) from (map_natCast PowerSeries.C 8).symm, PowerSeries.derivative_C]

lemma Dx_num_9 : Dx (9 : PowerSeries ℚ) = 0 := by
  rw [Dx, show (9 : PowerSeries ℚ) = PowerSeries.C (9 : ℚ) from (map_natCast PowerSeries.C 9).symm, PowerSeries.derivative_C]

lemma Dx_num_12 : Dx (12 : PowerSeries ℚ) = 0 := by
  rw [Dx, show (12 : PowerSeries ℚ) = PowerSeries.C (12 : ℚ) from (map_natCast PowerSeries.C 12).symm, PowerSeries.derivative_C]

lemma Dx_num_15 : Dx (15 : PowerSeries ℚ) = 0 := by
  rw [Dx, show (15 : PowerSeries ℚ) = PowerSeries.C (15 : ℚ) from (map_natCast PowerSeries.C 15).symm, PowerSeries.derivative_C]

lemma Dx_num_16 : Dx (16 : PowerSeries ℚ) = 0 := by
  rw [Dx, show (16 : PowerSeries ℚ) = PowerSeries.C (16 : ℚ) from (map_natCast PowerSeries.C 16).symm, PowerSeries.derivative_C]

lemma Dx_num_20 : Dx (20 : PowerSeries ℚ) = 0 := by
  rw [Dx, show (20 : PowerSeries ℚ) = PowerSeries.C (20 : ℚ) from (map_natCast PowerSeries.C 20).symm, PowerSeries.derivative_C]

lemma Dx_num_24 : Dx (24 : PowerSeries ℚ) = 0 := by
  rw [Dx, show (24 : PowerSeries ℚ) = PowerSeries.C (24 : ℚ) from (map_natCast PowerSeries.C 24).symm, PowerSeries.derivative_C]

lemma Dx_num_27 : Dx (27 : PowerSeries ℚ) = 0 := by
  rw [Dx, show (27 : PowerSeries ℚ) = PowerSeries.C (27 : ℚ) from (map_natCast PowerSeries.C 27).symm, PowerSeries.derivative_C]

lemma Dx_num_32 : Dx (32 : PowerSeries ℚ) = 0 := by
  rw [Dx, show (32 : PowerSeries ℚ) = PowerSeries.C (32 : ℚ) from (map_natCast PowerSeries.C 32).symm, PowerSeries.derivative_C]

lemma Dx_num_45 : Dx (45 : PowerSeries ℚ) = 0 := by
  rw [Dx, show (45 : PowerSeries ℚ) = PowerSeries.C (45 : ℚ) from (map_natCast PowerSeries.C 45).symm, PowerSeries.derivative_C]

lemma Dx_num_48 : Dx (48 : PowerSeries ℚ) = 0 := by
  rw [Dx, show (48 : PowerSeries ℚ) = PowerSeries.C (48 : ℚ) from (map_natCast PowerSeries.C 48).symm, PowerSeries.derivative_C]

lemma Dx_num_54 : Dx (54 : PowerSeries ℚ) = 0 := by
  rw [Dx, show (54 : PowerSeries ℚ) = PowerSeries.C (54 : ℚ) from (map_natCast PowerSeries.C 54).symm, PowerSeries.derivative_C]

lemma Dx_num_90 : Dx (90 : PowerSeries ℚ) = 0 := by
  rw [Dx, show (90 : PowerSeries ℚ) = PowerSeries.C (90 : ℚ) from (map_natCast PowerSeries.C 90).symm, PowerSeries.derivative_C]

lemma Dx_num_96 : Dx (96 : PowerSeries ℚ) = 0 := by
  rw [Dx, show (96 : PowerSeries ℚ) = PowerSeries.C (96 : ℚ) from (map_natCast PowerSeries.C 96).symm, PowerSeries.derivative_C]

lemma Dx_num_1 : Dx (1 : PowerSeries ℚ) = 0 := by
  rw [Dx, show (1 : PowerSeries ℚ) = PowerSeries.C (1 : ℚ) from (map_natCast PowerSeries.C 1).symm, PowerSeries.derivative_C]


lemma Dx_iterate (j : ℕ) (f : PowerSeries ℚ) :
    (Dx^[j]) f = ((PowerSeries.derivative (R := ℚ))^[j]) f := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      rfl

/-! ### Conversion of the `C`-constants used below -/


lemma C_z1 : PowerSeries.C ((1:ℤ):ℚ) = ((1:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 1
lemma C_zneg1 : PowerSeries.C (((-1):ℤ):ℚ) = (((-1):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-1)
lemma C_z2 : PowerSeries.C ((2:ℤ):ℚ) = ((2:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 2
lemma C_zneg2 : PowerSeries.C (((-2):ℤ):ℚ) = (((-2):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-2)
lemma C_z3 : PowerSeries.C ((3:ℤ):ℚ) = ((3:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 3
lemma C_zneg3 : PowerSeries.C (((-3):ℤ):ℚ) = (((-3):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-3)
lemma C_z4 : PowerSeries.C ((4:ℤ):ℚ) = ((4:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 4
lemma C_zneg4 : PowerSeries.C (((-4):ℤ):ℚ) = (((-4):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-4)
lemma C_z5 : PowerSeries.C ((5:ℤ):ℚ) = ((5:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 5
lemma C_zneg5 : PowerSeries.C (((-5):ℤ):ℚ) = (((-5):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-5)
lemma C_z6 : PowerSeries.C ((6:ℤ):ℚ) = ((6:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 6
lemma C_zneg6 : PowerSeries.C (((-6):ℤ):ℚ) = (((-6):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-6)
lemma C_z7 : PowerSeries.C ((7:ℤ):ℚ) = ((7:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 7
lemma C_zneg7 : PowerSeries.C (((-7):ℤ):ℚ) = (((-7):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-7)
lemma C_z8 : PowerSeries.C ((8:ℤ):ℚ) = ((8:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 8
lemma C_zneg8 : PowerSeries.C (((-8):ℤ):ℚ) = (((-8):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-8)
lemma C_z9 : PowerSeries.C ((9:ℤ):ℚ) = ((9:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 9
lemma C_zneg9 : PowerSeries.C (((-9):ℤ):ℚ) = (((-9):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-9)
lemma C_z12 : PowerSeries.C ((12:ℤ):ℚ) = ((12:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 12
lemma C_zneg12 : PowerSeries.C (((-12):ℤ):ℚ) = (((-12):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-12)
lemma C_z16 : PowerSeries.C ((16:ℤ):ℚ) = ((16:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 16
lemma C_zneg16 : PowerSeries.C (((-16):ℤ):ℚ) = (((-16):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-16)
lemma C_z20 : PowerSeries.C ((20:ℤ):ℚ) = ((20:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 20
lemma C_zneg20 : PowerSeries.C (((-20):ℤ):ℚ) = (((-20):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-20)
lemma C_z24 : PowerSeries.C ((24:ℤ):ℚ) = ((24:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 24
lemma C_zneg24 : PowerSeries.C (((-24):ℤ):ℚ) = (((-24):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-24)
lemma C_z27 : PowerSeries.C ((27:ℤ):ℚ) = ((27:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 27
lemma C_zneg27 : PowerSeries.C (((-27):ℤ):ℚ) = (((-27):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-27)
lemma C_z54 : PowerSeries.C ((54:ℤ):ℚ) = ((54:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 54
lemma C_zneg54 : PowerSeries.C (((-54):ℤ):ℚ) = (((-54):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-54)
lemma C_z68 : PowerSeries.C ((68:ℤ):ℚ) = ((68:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 68
lemma C_zneg68 : PowerSeries.C (((-68):ℤ):ℚ) = (((-68):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-68)
lemma C_z80 : PowerSeries.C ((80:ℤ):ℚ) = ((80:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 80
lemma C_zneg80 : PowerSeries.C (((-80):ℤ):ℚ) = (((-80):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-80)
lemma C_z744 : PowerSeries.C ((744:ℤ):ℚ) = ((744:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 744
lemma C_zneg744 : PowerSeries.C (((-744):ℤ):ℚ) = (((-744):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-744)
lemma C_z1612 : PowerSeries.C ((1612:ℤ):ℚ) = ((1612:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 1612
lemma C_zneg1612 : PowerSeries.C (((-1612):ℤ):ℚ) = (((-1612):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-1612)
lemma C_z2268 : PowerSeries.C ((2268:ℤ):ℚ) = ((2268:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 2268
lemma C_zneg2268 : PowerSeries.C (((-2268):ℤ):ℚ) = (((-2268):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-2268)
lemma C_z5522 : PowerSeries.C ((5522:ℤ):ℚ) = ((5522:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 5522
lemma C_zneg5522 : PowerSeries.C (((-5522):ℤ):ℚ) = (((-5522):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-5522)
lemma C_z6480 : PowerSeries.C ((6480:ℤ):ℚ) = ((6480:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 6480
lemma C_zneg6480 : PowerSeries.C (((-6480):ℤ):ℚ) = (((-6480):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-6480)
lemma C_z10368 : PowerSeries.C ((10368:ℤ):ℚ) = ((10368:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 10368
lemma C_zneg10368 : PowerSeries.C (((-10368):ℤ):ℚ) = (((-10368):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-10368)
lemma C_z12706 : PowerSeries.C ((12706:ℤ):ℚ) = ((12706:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 12706
lemma C_zneg12706 : PowerSeries.C (((-12706):ℤ):ℚ) = (((-12706):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-12706)
lemma C_z12816 : PowerSeries.C ((12816:ℤ):ℚ) = ((12816:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 12816
lemma C_zneg12816 : PowerSeries.C (((-12816):ℤ):ℚ) = (((-12816):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-12816)
lemma C_z41472 : PowerSeries.C ((41472:ℤ):ℚ) = ((41472:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 41472
lemma C_zneg41472 : PowerSeries.C (((-41472):ℤ):ℚ) = (((-41472):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-41472)
lemma C_z82944 : PowerSeries.C ((82944:ℤ):ℚ) = ((82944:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 82944
lemma C_zneg82944 : PowerSeries.C (((-82944):ℤ):ℚ) = (((-82944):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-82944)
lemma C_z91584 : PowerSeries.C ((91584:ℤ):ℚ) = ((91584:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 91584
lemma C_zneg91584 : PowerSeries.C (((-91584):ℤ):ℚ) = (((-91584):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-91584)
lemma C_z133615 : PowerSeries.C ((133615:ℤ):ℚ) = ((133615:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 133615
lemma C_zneg133615 : PowerSeries.C (((-133615):ℤ):ℚ) = (((-133615):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-133615)
lemma C_z145152 : PowerSeries.C ((145152:ℤ):ℚ) = ((145152:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 145152
lemma C_zneg145152 : PowerSeries.C (((-145152):ℤ):ℚ) = (((-145152):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-145152)
lemma C_z191232 : PowerSeries.C ((191232:ℤ):ℚ) = ((191232:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 191232
lemma C_zneg191232 : PowerSeries.C (((-191232):ℤ):ℚ) = (((-191232):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-191232)
lemma C_z205186 : PowerSeries.C ((205186:ℤ):ℚ) = ((205186:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 205186
lemma C_zneg205186 : PowerSeries.C (((-205186):ℤ):ℚ) = (((-205186):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-205186)
lemma C_z243382 : PowerSeries.C ((243382:ℤ):ℚ) = ((243382:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 243382
lemma C_zneg243382 : PowerSeries.C (((-243382):ℤ):ℚ) = (((-243382):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-243382)
lemma C_z283264 : PowerSeries.C ((283264:ℤ):ℚ) = ((283264:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 283264
lemma C_zneg283264 : PowerSeries.C (((-283264):ℤ):ℚ) = (((-283264):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-283264)
lemma C_z352824 : PowerSeries.C ((352824:ℤ):ℚ) = ((352824:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 352824
lemma C_zneg352824 : PowerSeries.C (((-352824):ℤ):ℚ) = (((-352824):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-352824)
lemma C_z560656 : PowerSeries.C ((560656:ℤ):ℚ) = ((560656:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 560656
lemma C_zneg560656 : PowerSeries.C (((-560656):ℤ):ℚ) = (((-560656):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-560656)
lemma C_z617472 : PowerSeries.C ((617472:ℤ):ℚ) = ((617472:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 617472
lemma C_zneg617472 : PowerSeries.C (((-617472):ℤ):ℚ) = (((-617472):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-617472)
lemma C_z876672 : PowerSeries.C ((876672:ℤ):ℚ) = ((876672:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 876672
lemma C_zneg876672 : PowerSeries.C (((-876672):ℤ):ℚ) = (((-876672):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-876672)
lemma C_z945968 : PowerSeries.C ((945968:ℤ):ℚ) = ((945968:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 945968
lemma C_zneg945968 : PowerSeries.C (((-945968):ℤ):ℚ) = (((-945968):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-945968)
lemma C_z1380710 : PowerSeries.C ((1380710:ℤ):ℚ) = ((1380710:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 1380710
lemma C_zneg1380710 : PowerSeries.C (((-1380710):ℤ):ℚ) = (((-1380710):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-1380710)
lemma C_z1411958 : PowerSeries.C ((1411958:ℤ):ℚ) = ((1411958:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 1411958
lemma C_zneg1411958 : PowerSeries.C (((-1411958):ℤ):ℚ) = (((-1411958):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-1411958)
lemma C_z1436676 : PowerSeries.C ((1436676:ℤ):ℚ) = ((1436676:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 1436676
lemma C_zneg1436676 : PowerSeries.C (((-1436676):ℤ):ℚ) = (((-1436676):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-1436676)
lemma C_z1735752 : PowerSeries.C ((1735752:ℤ):ℚ) = ((1735752:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 1735752
lemma C_zneg1735752 : PowerSeries.C (((-1735752):ℤ):ℚ) = (((-1735752):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-1735752)
lemma C_z2131226 : PowerSeries.C ((2131226:ℤ):ℚ) = ((2131226:ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C 2131226
lemma C_zneg2131226 : PowerSeries.C (((-2131226):ℤ):ℚ) = (((-2131226):ℤ) : PowerSeries ℚ) := map_intCast PowerSeries.C (-2131226)

macro "clearc" : tactic => `(tactic| simp only [Submission.CDT.C_z1, Submission.CDT.C_zneg1, Submission.CDT.C_z2, Submission.CDT.C_zneg2, Submission.CDT.C_z3, Submission.CDT.C_zneg3, Submission.CDT.C_z4, Submission.CDT.C_zneg4, Submission.CDT.C_z5, Submission.CDT.C_zneg5, Submission.CDT.C_z6, Submission.CDT.C_zneg6, Submission.CDT.C_z7, Submission.CDT.C_zneg7, Submission.CDT.C_z8, Submission.CDT.C_zneg8, Submission.CDT.C_z9, Submission.CDT.C_zneg9, Submission.CDT.C_z12, Submission.CDT.C_zneg12, Submission.CDT.C_z16, Submission.CDT.C_zneg16, Submission.CDT.C_z20, Submission.CDT.C_zneg20, Submission.CDT.C_z24, Submission.CDT.C_zneg24, Submission.CDT.C_z27, Submission.CDT.C_zneg27, Submission.CDT.C_z54, Submission.CDT.C_zneg54, Submission.CDT.C_z68, Submission.CDT.C_zneg68, Submission.CDT.C_z80, Submission.CDT.C_zneg80, Submission.CDT.C_z744, Submission.CDT.C_zneg744, Submission.CDT.C_z1612, Submission.CDT.C_zneg1612, Submission.CDT.C_z2268, Submission.CDT.C_zneg2268, Submission.CDT.C_z5522, Submission.CDT.C_zneg5522, Submission.CDT.C_z6480, Submission.CDT.C_zneg6480, Submission.CDT.C_z10368, Submission.CDT.C_zneg10368, Submission.CDT.C_z12706, Submission.CDT.C_zneg12706, Submission.CDT.C_z12816, Submission.CDT.C_zneg12816, Submission.CDT.C_z41472, Submission.CDT.C_zneg41472, Submission.CDT.C_z82944, Submission.CDT.C_zneg82944, Submission.CDT.C_z91584, Submission.CDT.C_zneg91584, Submission.CDT.C_z133615, Submission.CDT.C_zneg133615, Submission.CDT.C_z145152, Submission.CDT.C_zneg145152, Submission.CDT.C_z191232, Submission.CDT.C_zneg191232, Submission.CDT.C_z205186, Submission.CDT.C_zneg205186, Submission.CDT.C_z243382, Submission.CDT.C_zneg243382, Submission.CDT.C_z283264, Submission.CDT.C_zneg283264, Submission.CDT.C_z352824, Submission.CDT.C_zneg352824, Submission.CDT.C_z560656, Submission.CDT.C_zneg560656, Submission.CDT.C_z617472, Submission.CDT.C_zneg617472, Submission.CDT.C_z876672, Submission.CDT.C_zneg876672, Submission.CDT.C_z945968, Submission.CDT.C_zneg945968, Submission.CDT.C_z1380710, Submission.CDT.C_zneg1380710, Submission.CDT.C_z1411958, Submission.CDT.C_zneg1411958, Submission.CDT.C_z1436676, Submission.CDT.C_zneg1436676, Submission.CDT.C_z1735752, Submission.CDT.C_zneg1735752, Submission.CDT.C_z2131226, Submission.CDT.C_zneg2131226])


macro "dxsimp" : tactic => `(tactic| simp only [Submission.CDT.Dx_mul, Submission.CDT.Dx_add, Submission.CDT.Dx_sub, Submission.CDT.Dx_neg, Submission.CDT.Dx_one, Submission.CDT.Dx_X, Submission.CDT.Dx_C_int, Submission.CDT.Dx_pow, Submission.CDT.Dx_num_2, Submission.CDT.Dx_num_3, Submission.CDT.Dx_num_4, Submission.CDT.Dx_num_5, Submission.CDT.Dx_num_6, Submission.CDT.Dx_num_8, Submission.CDT.Dx_num_9, Submission.CDT.Dx_num_12, Submission.CDT.Dx_num_15, Submission.CDT.Dx_num_16, Submission.CDT.Dx_num_20, Submission.CDT.Dx_num_24, Submission.CDT.Dx_num_27, Submission.CDT.Dx_num_32, Submission.CDT.Dx_num_45, Submission.CDT.Dx_num_48, Submission.CDT.Dx_num_54, Submission.CDT.Dx_num_90, Submission.CDT.Dx_num_96, Submission.CDT.Dx_num_1, smul_eq_mul])


/-! ## 1. The ODE coefficients and their derivatives -/

/-- `a₂ = x(1−x)(1−9x)`, the `u″`-coefficient of `HA_ode` -/
def a2c : PowerSeries ℚ := X * (1 - X) * (1 - PowerSeries.C ((9 : ℤ) : ℚ) * X)
/-- `a₁ = 1−20x+27x²` -/
def a1c : PowerSeries ℚ :=
  1 - PowerSeries.C ((20 : ℤ) : ℚ) * X + PowerSeries.C ((27 : ℤ) : ℚ) * X ^ 2
/-- `a₀ = 3(3x−1)` -/
def a0c : PowerSeries ℚ := PowerSeries.C ((3 : ℤ) : ℚ) * (PowerSeries.C ((3 : ℤ) : ℚ) * X - 1)
/-- `a₁′ = −20+54x` -/
def da1c : PowerSeries ℚ := -PowerSeries.C ((20 : ℤ) : ℚ) + PowerSeries.C ((54 : ℤ) : ℚ) * X
/-- `a₀′ = 9` -/
def da0c : PowerSeries ℚ := PowerSeries.C ((9 : ℤ) : ℚ)
/-- `a₁″ = 54` -/
def dda1c : PowerSeries ℚ := PowerSeries.C ((54 : ℤ) : ℚ)

lemma deriv_a2c : Dx a2c = a1c := by
  simp only [a2c, a1c]
  dxsimp
  clearc
  ring

lemma deriv_a1c : Dx a1c = da1c := by
  simp only [a1c, da1c]
  dxsimp
  clearc
  ring

lemma deriv_a0c : Dx a0c = da0c := by
  simp only [a0c, da0c]
  dxsimp
  clearc
  ring

lemma deriv_da1c : Dx da1c = dda1c := by
  simp only [da1c, dda1c]
  dxsimp
  clearc
  ring

lemma deriv_da0c : Dx da0c = 0 := by
  simp only [da0c]
  dxsimp

/-- `N₂ = x(8x+1)(x−1)²`, the `v″`-coefficient of the pulled-back ODE -/
def N2c : PowerSeries ℚ := X * (8 * X + 1) * (X - 1) ^ 2
/-- `N₁ = (8x²−16x−1)(x−1)` -/
def N1c : PowerSeries ℚ := (8 * X ^ 2 - 16 * X - 1) * (X - 1)
/-- `N₀ = 3(2x+1)` -/
def N0c : PowerSeries ℚ := 3 * (2 * X + 1)
/-- `N₂′ = 32x³ − 45x² + 12x + 1` -/
def dN2c : PowerSeries ℚ := 32 * X ^ 3 - 45 * X ^ 2 + 12 * X + 1
/-- `N₁′ = 24x² − 48x + 15` -/
def dN1c : PowerSeries ℚ := 24 * X ^ 2 - 48 * X + 15
/-- `N₀′ = 6` -/
def dN0c : PowerSeries ℚ := 6
/-- `N₂″ = 96x² − 90x + 12` -/
def ddN2c : PowerSeries ℚ := 96 * X ^ 2 - 90 * X + 12
/-- `N₁″ = 48x − 48` -/
def ddN1c : PowerSeries ℚ := 48 * X - 48

lemma deriv_N2c : Dx N2c = dN2c := by
  simp only [N2c, dN2c]
  dxsimp
  ring

lemma deriv_N1c : Dx N1c = dN1c := by
  simp only [N1c, dN1c]
  dxsimp
  ring

lemma deriv_N0c : Dx N0c = dN0c := by
  simp only [N0c, dN0c]
  dxsimp
  ring

lemma deriv_dN2c : Dx dN2c = ddN2c := by
  simp only [dN2c, ddN2c]
  dxsimp
  ring

lemma deriv_dN1c : Dx dN1c = ddN1c := by
  simp only [dN1c, ddN1c]
  dxsimp
  ring

lemma deriv_dN0c : Dx dN0c = 0 := by
  simp only [dN0c]
  dxsimp

lemma a2c_ne_zero : a2c ≠ 0 := by
  simp only [a2c]
  refine mul_ne_zero (mul_ne_zero X_ne_zero ?_) ?_
  · intro h
    have h0 := congrArg PowerSeries.constantCoeff h
    simp at h0
  · intro h
    have h0 := congrArg PowerSeries.constantCoeff h
    simp at h0

lemma N2c_ne_zero : N2c ≠ 0 := by
  simp only [N2c]
  refine mul_ne_zero (mul_ne_zero X_ne_zero ?_) ?_
  · intro h
    have h0 := congrArg PowerSeries.constantCoeff h
    simp at h0
  · intro h
    have h0 := congrArg PowerSeries.constantCoeff h
    simp at h0

/-! ## 2. The two second-order ODEs -/

lemma u_ode : a2c * Dx (Dx HA) + a1c * Dx HA + a0c * HA = 0 := by
  have h : a2c * Dx (Dx HA) + a1c * Dx HA + a0c * HA
      = X * (1 - X) * (1 - PowerSeries.C 9 * X)
          * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ)) HA)
        + (1 - PowerSeries.C 20 * X + PowerSeries.C 27 * X ^ 2)
          * (PowerSeries.derivative (R := ℚ)) HA
        + PowerSeries.C 3 * (PowerSeries.C 3 * X - 1) * HA := rfl
  rw [h, ← HA_odeLHS_eq]
  exact HA_ode

lemma v_ode : N2c * Dx (Dx (HA.subst sympPhi)) + N1c * Dx (HA.subst sympPhi)
    + N0c * (HA.subst sympPhi) = 0 := by
  have hL : Commons.Analysis.Differential.ode_pb_L HA = 0 := by
    rw [ode_pb_L_eq]; exact HA_ode
  have h := Commons.Analysis.Differential.ode_pullback_involution HA hL
  have h' : N2c * Dx (Dx (HA.subst sympPhi)) + N1c * Dx (HA.subst sympPhi)
      + N0c * (HA.subst sympPhi)
      = PowerSeries.X * (8 * PowerSeries.X + 1) * (PowerSeries.X - 1) ^ 2
          * (PowerSeries.derivative (R := ℚ)) ((PowerSeries.derivative (R := ℚ))
              (HA.subst (PowerSeries.X * (PowerSeries.X - 1)⁻¹)))
        + ((8 * PowerSeries.X ^ 2 - 16 * PowerSeries.X - 1) * (PowerSeries.X - 1))
          * (PowerSeries.derivative (R := ℚ)) (HA.subst (PowerSeries.X * (PowerSeries.X - 1)⁻¹))
        + (3 * (2 * PowerSeries.X + 1))
          * (HA.subst (PowerSeries.X * (PowerSeries.X - 1)⁻¹)) := rfl
  rw [h']
  exact h

/-! ## 3. The ODE chains -/

/-- the `u′`-coefficient of the chain `a₂²u‴ = r₂u′ + s₂u` equals `−r₂` -/
lemma A1u_eq : a2c * da1c + a2c * a0c - 2 * a1c ^ 2 =
    - (891 * X ^ 4 - 1323 * X ^ 3 + 615 * X ^ 2 - 57 * X + 2 : PowerSeries ℚ) := by
  simp only [a2c, a1c, a0c, da1c]
  clearc
  ring

/-- the `u`-coefficient of the chain `a₂²u‴ = r₂u′ + s₂u` equals `−s₂` -/
lemma A0u_eq : a2c * da0c - 2 * a1c * a0c =
    - (405 * X ^ 3 - 432 * X ^ 2 + 129 * X - 6 : PowerSeries ℚ) := by
  simp only [a2c, a1c, a0c, da0c]
  clearc
  ring

/-- the `u′`-coefficient of the chain `a₂³u⁗ = r₃u′ + s₃u` equals `−r₃` -/
lemma B1u_eq : a2c ^ 2 * dda1c + 2 * a2c ^ 2 * da0c - 6 * a2c * a1c * da1c
      - 4 * a2c * a1c * a0c + 6 * a1c ^ 3
    = - (-36450 * X ^ 6 + 81324 * X ^ 5 - 71658 * X ^ 4 + 26928 * X ^ 3 - 3438 * X ^ 2
        + 228 * X - 6 : PowerSeries ℚ) := by
  simp only [a2c, a1c, a0c, da1c, da0c, dda1c]
  clearc
  ring

/-- the `u`-coefficient of the chain `a₂³u⁗ = r₃u′ + s₃u` equals `−s₃` -/
lemma B0u_eq : -3 * a2c * a1c * da0c - 3 * a2c * a0c * da1c - a2c * a0c ^ 2
      + 6 * a1c ^ 2 * a0c
    = - (-18954 * X ^ 5 + 34182 * X ^ 4 - 23544 * X ^ 3 + 6552 * X ^ 2 - 558 * X
        + 18 : PowerSeries ℚ) := by
  simp only [a2c, a1c, a0c, da1c, da0c]
  clearc
  ring

/-- `r₂` for the Franel ODE -/
def r2c : PowerSeries ℚ := 891 * X ^ 4 - 1323 * X ^ 3 + 615 * X ^ 2 - 57 * X + 2
/-- `s₂` for the Franel ODE -/
def s2c : PowerSeries ℚ := 405 * X ^ 3 - 432 * X ^ 2 + 129 * X - 6
/-- `r₃` for the Franel ODE -/
def r3c : PowerSeries ℚ :=
  -36450 * X ^ 6 + 81324 * X ^ 5 - 71658 * X ^ 4 + 26928 * X ^ 3 - 3438 * X ^ 2 + 228 * X - 6
/-- `s₃` for the Franel ODE -/
def s3c : PowerSeries ℚ :=
  -18954 * X ^ 5 + 34182 * X ^ 4 - 23544 * X ^ 3 + 6552 * X ^ 2 - 558 * X + 18

macro "dxode" : tactic => `(tactic| simp only [Submission.CDT.Dx_mul, Submission.CDT.Dx_add, Submission.CDT.Dx_sub, Submission.CDT.Dx_neg, Submission.CDT.Dx_one, Submission.CDT.Dx_X, Submission.CDT.Dx_C_int, Submission.CDT.Dx_pow, Submission.CDT.Dx_num_2, Submission.CDT.Dx_num_3, Submission.CDT.Dx_num_4, Submission.CDT.Dx_num_5, Submission.CDT.Dx_num_6, Submission.CDT.Dx_num_8, Submission.CDT.Dx_num_9, Submission.CDT.Dx_num_12, Submission.CDT.Dx_num_15, Submission.CDT.Dx_num_16, Submission.CDT.Dx_num_20, Submission.CDT.Dx_num_24, Submission.CDT.Dx_num_27, Submission.CDT.Dx_num_32, Submission.CDT.Dx_num_45, Submission.CDT.Dx_num_48, Submission.CDT.Dx_num_54, Submission.CDT.Dx_num_90, Submission.CDT.Dx_num_96, Submission.CDT.Dx_num_1, smul_eq_mul, deriv_a2c, deriv_a1c, deriv_a0c, deriv_da1c, deriv_da0c, deriv_N2c, deriv_N1c, deriv_N0c, deriv_dN2c, deriv_dN1c, deriv_dN0c])

/-- the first derivative of the Franel ODE -/
lemma deriv_ode_u (f : PowerSeries ℚ) :
    Dx (a2c * Dx (Dx f) + a1c * Dx f + a0c * f)
      = a2c * Dx (Dx (Dx f)) + (a1c + a1c) * Dx (Dx f)
        + (da1c + a0c) * Dx f + da0c * f := by
  dxode
  ring

/-- the second derivative of the Franel ODE -/
lemma deriv_ode_u2 (f : PowerSeries ℚ) :
    Dx (a2c * Dx (Dx (Dx f)) + (a1c + a1c) * Dx (Dx f) + (da1c + a0c) * Dx f + da0c * f)
      = a2c * Dx (Dx (Dx (Dx f))) + 3 * (a1c * Dx (Dx (Dx f)))
        + (3 * da1c + a0c) * Dx (Dx f) + (dda1c + 2 * da0c) * Dx f := by
  dxode
  ring

lemma u_chain2 (f : PowerSeries ℚ)
    (h : a2c * Dx (Dx f) + a1c * Dx f + a0c * f = 0) :
    a2c ^ 2 * Dx (Dx (Dx f)) = r2c * Dx f + s2c * f := by
  have hd : a2c * Dx (Dx (Dx f)) + (a1c + a1c) * Dx (Dx f) + (da1c + a0c) * Dx f
      + da0c * f = 0 := by
    rw [← deriv_ode_u f, h, Dx_zero]
  have e1 : a2c * da1c + a2c * a0c - 2 * a1c ^ 2 = -r2c := by rw [A1u_eq]; rfl
  have e0 : a2c * da0c - 2 * a1c * a0c = -s2c := by rw [A0u_eq]; rfl
  linear_combination (norm := ring) a2c * hd - (a1c + a1c) * h - (Dx f) * e1 - f * e0

lemma u_chain3 (f : PowerSeries ℚ)
    (h : a2c * Dx (Dx f) + a1c * Dx f + a0c * f = 0) :
    a2c ^ 3 * Dx (Dx (Dx (Dx f))) = r3c * Dx f + s3c * f := by
  have hd1 : a2c * Dx (Dx (Dx f)) + (a1c + a1c) * Dx (Dx f) + (da1c + a0c) * Dx f
      + da0c * f = 0 := by
    rw [← deriv_ode_u f, h, Dx_zero]
  have hd2 : a2c * Dx (Dx (Dx (Dx f))) + 3 * (a1c * Dx (Dx (Dx f)))
      + (3 * da1c + a0c) * Dx (Dx f) + (dda1c + 2 * da0c) * Dx f = 0 := by
    rw [← deriv_ode_u2 f, hd1, Dx_zero]
  have e1 : a2c ^ 2 * dda1c + 2 * a2c ^ 2 * da0c - 6 * a2c * a1c * da1c
      - 4 * a2c * a1c * a0c + 6 * a1c ^ 3 = -r3c := by rw [B1u_eq]; rfl
  have e0 : -3 * a2c * a1c * da0c - 3 * a2c * a0c * da1c - a2c * a0c ^ 2
      + 6 * a1c ^ 2 * a0c = -s3c := by rw [B0u_eq]; rfl
  linear_combination (norm := ring) a2c ^ 2 * hd2 - (3 * a2c * a1c) * hd1
    + (-a2c * (3 * da1c + a0c) + 6 * a1c ^ 2) * h - (Dx f) * e1 - f * e0

/-! ### The same for the pulled-back ODE (`v`-side) -/

/-- the `v′`-coefficient of the chain `N₂²v‴ = r₂v′ + s₂v` equals `−r₂` -/
lemma A1v_eq : N2c * dN1c + N2c * N0c - dN2c * N1c - N1c ^ 2
    = - ((X - 1) ^ 2 * (128 * X ^ 4 - 560 * X ^ 3 + 306 * X ^ 2 + 43 * X
        + 2) : PowerSeries ℚ) := by
  simp only [N2c, N1c, N0c, dN2c, dN1c]
  ring

/-- the `v`-coefficient of the chain `N₂²v‴ = r₂v′ + s₂v` equals `−s₂` -/
lemma A0v_eq : N2c * dN0c - dN2c * N0c - N1c * N0c
    = - (3 * (X - 1) * (64 * X ^ 3 - 4 * X ^ 2 - 31 * X - 2) : PowerSeries ℚ) := by
  simp only [N2c, N1c, N0c, dN2c, dN0c]
  ring

/-- the `v′`-coefficient of the chain `N₂³v⁗ = r₃v′ + s₃v` equals `−r₃` -/
lemma B1v_eq : N2c ^ 2 * (ddN1c + 2 * dN0c) - N2c * (2 * dN2c + N1c) * (dN1c + N0c)
      + (-N2c * (ddN2c + 2 * dN1c + N0c) + (2 * dN2c + N1c) * (dN2c + N1c)) * N1c
    = - (-6 * (X - 1) ^ 3 * (512 * X ^ 6 - 3584 * X ^ 5 + 4192 * X ^ 4 - 1060 * X ^ 3
        - 274 * X ^ 2 - 28 * X - 1) : PowerSeries ℚ) := by
  simp only [N2c, N1c, N0c, dN2c, dN1c, dN0c, ddN2c, ddN1c]
  ring

/-- the `v`-coefficient of the chain `N₂³v⁗ = r₃v′ + s₃v` equals `−s₃` -/
lemma B0v_eq : -N2c * (2 * dN2c + N1c) * dN0c
      + (-N2c * (ddN2c + 2 * dN1c + N0c) + (2 * dN2c + N1c) * (dN2c + N1c)) * N0c
    = - (-18 * (X - 1) ^ 2 * (384 * X ^ 5 - 256 * X ^ 4 - 220 * X ^ 3 + 150 * X ^ 2
        + 22 * X + 1) : PowerSeries ℚ) := by
  simp only [N2c, N1c, N0c, dN2c, dN1c, dN0c, ddN2c, ddN1c]
  ring

/-- `r₂` for the pulled-back ODE -/
def r2v : PowerSeries ℚ := (X - 1) ^ 2 * (128 * X ^ 4 - 560 * X ^ 3 + 306 * X ^ 2 + 43 * X + 2)
/-- `s₂` for the pulled-back ODE -/
def s2v : PowerSeries ℚ := 3 * (X - 1) * (64 * X ^ 3 - 4 * X ^ 2 - 31 * X - 2)
/-- `r₃` for the pulled-back ODE -/
def r3v : PowerSeries ℚ := -6 * (X - 1) ^ 3
  * (512 * X ^ 6 - 3584 * X ^ 5 + 4192 * X ^ 4 - 1060 * X ^ 3 - 274 * X ^ 2 - 28 * X - 1)
/-- `s₃` for the pulled-back ODE -/
def s3v : PowerSeries ℚ := -18 * (X - 1) ^ 2
  * (384 * X ^ 5 - 256 * X ^ 4 - 220 * X ^ 3 + 150 * X ^ 2 + 22 * X + 1)

/-- the first derivative of the pulled-back ODE -/
lemma deriv_ode_v (f : PowerSeries ℚ) :
    Dx (N2c * Dx (Dx f) + N1c * Dx f + N0c * f)
      = N2c * Dx (Dx (Dx f)) + (dN2c + N1c) * Dx (Dx f)
        + (dN1c + N0c) * Dx f + dN0c * f := by
  dxode
  ring

/-- the second derivative of the pulled-back ODE -/
lemma deriv_ode_v2 (f : PowerSeries ℚ) :
    Dx (N2c * Dx (Dx (Dx f)) + (dN2c + N1c) * Dx (Dx f) + (dN1c + N0c) * Dx f + dN0c * f)
      = N2c * Dx (Dx (Dx (Dx f))) + (2 * dN2c + N1c) * Dx (Dx (Dx f))
        + (ddN2c + 2 * dN1c + N0c) * Dx (Dx f) + (ddN1c + 2 * dN0c) * Dx f := by
  dxode
  ring

lemma v_chain2 (f : PowerSeries ℚ)
    (h : N2c * Dx (Dx f) + N1c * Dx f + N0c * f = 0) :
    N2c ^ 2 * Dx (Dx (Dx f)) = r2v * Dx f + s2v * f := by
  have hd : N2c * Dx (Dx (Dx f)) + (dN2c + N1c) * Dx (Dx f) + (dN1c + N0c) * Dx f
      + dN0c * f = 0 := by
    rw [← deriv_ode_v f, h, Dx_zero]
  have e1 : N2c * dN1c + N2c * N0c - dN2c * N1c - N1c ^ 2 = -r2v := by rw [A1v_eq]; rfl
  have e0 : N2c * dN0c - dN2c * N0c - N1c * N0c = -s2v := by rw [A0v_eq]; rfl
  linear_combination (norm := ring) N2c * hd - (dN2c + N1c) * h - (Dx f) * e1 - f * e0

lemma v_chain3 (f : PowerSeries ℚ)
    (h : N2c * Dx (Dx f) + N1c * Dx f + N0c * f = 0) :
    N2c ^ 3 * Dx (Dx (Dx (Dx f))) = r3v * Dx f + s3v * f := by
  have hd1 : N2c * Dx (Dx (Dx f)) + (dN2c + N1c) * Dx (Dx f) + (dN1c + N0c) * Dx f
      + dN0c * f = 0 := by
    rw [← deriv_ode_v f, h, Dx_zero]
  have hd2 : N2c * Dx (Dx (Dx (Dx f))) + (2 * dN2c + N1c) * Dx (Dx (Dx f))
      + (ddN2c + 2 * dN1c + N0c) * Dx (Dx f) + (ddN1c + 2 * dN0c) * Dx f = 0 := by
    rw [← deriv_ode_v2 f, hd1, Dx_zero]
  have e1 : N2c ^ 2 * (ddN1c + 2 * dN0c) - N2c * (2 * dN2c + N1c) * (dN1c + N0c)
      + (-N2c * (ddN2c + 2 * dN1c + N0c) + (2 * dN2c + N1c) * (dN2c + N1c)) * N1c
      = -r3v := by rw [B1v_eq]; rfl
  have e0 : -N2c * (2 * dN2c + N1c) * dN0c
      + (-N2c * (ddN2c + 2 * dN1c + N0c) + (2 * dN2c + N1c) * (dN2c + N1c)) * N0c
      = -s3v := by rw [B0v_eq]; rfl
  linear_combination (norm := ring) N2c ^ 2 * hd2 - (N2c * (2 * dN2c + N1c)) * hd1
    + (-N2c * (ddN2c + 2 * dN1c + N0c) + (2 * dN2c + N1c) * (dN2c + N1c)) * h
    - (Dx f) * e1 - f * e0

/-! ## 4. The reduction: `Σ_j Mp_j·F₀⁽ʲ⁾ = 0` -/

lemma reduce_u (f : PowerSeries ℚ)
    (h : a2c * Dx (Dx f) + a1c * Dx f + a0c * f = 0) :
    Mp0 * f + Mp1 * Dx f + Mp2 * Dx (Dx f) + Mp3 * Dx (Dx (Dx f))
      + Mp4 * Dx (Dx (Dx (Dx f))) = 0 := by
  have h1 : a2c * Dx (Dx f) = -(a1c * Dx f) - a0c * f := by linear_combination h
  have h2 := u_chain2 f h
  have h3 := u_chain3 f h
  have hz1 : Mp1 * a2c ^ 4 - Mp2 * a2c ^ 3 * a1c + Mp3 * a2c ^ 2 * r2c + Mp4 * a2c * r3c = 0 := by
    unfold Mp1 Mp2 Mp3 Mp4 P1 P2 P3 P4 Ad a2c a1c r2c r3c
    clearc
    ring
  have hz0 : Mp0 * a2c ^ 4 - Mp2 * a2c ^ 3 * a0c + Mp3 * a2c ^ 2 * s2c + Mp4 * a2c * s3c = 0 := by
    unfold Mp0 Mp2 Mp3 Mp4 P0 P2 P3 P4 Ad a2c a0c s2c s3c
    clearc
    ring
  have key : a2c ^ 4 * (Mp0 * f + Mp1 * Dx f + Mp2 * Dx (Dx f) + Mp3 * Dx (Dx (Dx f))
        + Mp4 * Dx (Dx (Dx (Dx f)))) = 0 := by
    rw [mul_add, mul_add, mul_add, mul_add,
      show a2c ^ 4 * (Mp2 * Dx (Dx f)) = Mp2 * (a2c ^ 3 * (a2c * Dx (Dx f))) by ring, h1,
      show a2c ^ 4 * (Mp3 * Dx (Dx (Dx f))) = Mp3 * (a2c ^ 2 * (a2c ^ 2 * Dx (Dx (Dx f)))) by ring,
      h2,
      show a2c ^ 4 * (Mp4 * Dx (Dx (Dx (Dx f))))
          = Mp4 * (a2c * (a2c ^ 3 * Dx (Dx (Dx (Dx f))))) by ring, h3]
    have expand : a2c ^ 4 * (Mp0 * f) + a2c ^ 4 * (Mp1 * Dx f)
          + Mp2 * (a2c ^ 3 * (-(a1c * Dx f) - a0c * f))
          + Mp3 * (a2c ^ 2 * (r2c * Dx f + s2c * f))
          + Mp4 * (a2c * (r3c * Dx f + s3c * f))
        = (Mp1 * a2c ^ 4 - Mp2 * a2c ^ 3 * a1c + Mp3 * a2c ^ 2 * r2c + Mp4 * a2c * r3c) * Dx f
          + (Mp0 * a2c ^ 4 - Mp2 * a2c ^ 3 * a0c + Mp3 * a2c ^ 2 * s2c + Mp4 * a2c * s3c) * f := by
      ring
    rw [expand, hz1, hz0, zero_mul, zero_mul, add_zero]
  exact mul_left_cancel₀ (pow_ne_zero 4 a2c_ne_zero) (by rw [key, mul_zero])

lemma reduce_v (f : PowerSeries ℚ)
    (h : N2c * Dx (Dx f) + N1c * Dx f + N0c * f = 0) :
    Mp0 * f + Mp1 * Dx f + Mp2 * Dx (Dx f) + Mp3 * Dx (Dx (Dx f))
      + Mp4 * Dx (Dx (Dx (Dx f))) = 0 := by
  have h1 : N2c * Dx (Dx f) = -(N1c * Dx f) - N0c * f := by linear_combination h
  have h2 := v_chain2 f h
  have h3 := v_chain3 f h
  have hz1 : Mp1 * N2c ^ 4 - Mp2 * N2c ^ 3 * N1c + Mp3 * N2c ^ 2 * r2v + Mp4 * N2c * r3v = 0 := by
    unfold Mp1 Mp2 Mp3 Mp4 P1 P2 P3 P4 Ad N2c N1c r2v r3v
    clearc
    ring
  have hz0 : Mp0 * N2c ^ 4 - Mp2 * N2c ^ 3 * N0c + Mp3 * N2c ^ 2 * s2v + Mp4 * N2c * s3v = 0 := by
    unfold Mp0 Mp2 Mp3 Mp4 P0 P2 P3 P4 Ad N2c N0c s2v s3v
    clearc
    ring
  have key : N2c ^ 4 * (Mp0 * f + Mp1 * Dx f + Mp2 * Dx (Dx f) + Mp3 * Dx (Dx (Dx f))
        + Mp4 * Dx (Dx (Dx (Dx f)))) = 0 := by
    rw [mul_add, mul_add, mul_add, mul_add,
      show N2c ^ 4 * (Mp2 * Dx (Dx f)) = Mp2 * (N2c ^ 3 * (N2c * Dx (Dx f))) by ring, h1,
      show N2c ^ 4 * (Mp3 * Dx (Dx (Dx f))) = Mp3 * (N2c ^ 2 * (N2c ^ 2 * Dx (Dx (Dx f)))) by ring,
      h2,
      show N2c ^ 4 * (Mp4 * Dx (Dx (Dx (Dx f))))
          = Mp4 * (N2c * (N2c ^ 3 * Dx (Dx (Dx (Dx f))))) by ring, h3]
    have expand : N2c ^ 4 * (Mp0 * f) + N2c ^ 4 * (Mp1 * Dx f)
          + Mp2 * (N2c ^ 3 * (-(N1c * Dx f) - N0c * f))
          + Mp3 * (N2c ^ 2 * (r2v * Dx f + s2v * f))
          + Mp4 * (N2c * (r3v * Dx f + s3v * f))
        = (Mp1 * N2c ^ 4 - Mp2 * N2c ^ 3 * N1c + Mp3 * N2c ^ 2 * r2v + Mp4 * N2c * r3v) * Dx f
          + (Mp0 * N2c ^ 4 - Mp2 * N2c ^ 3 * N0c + Mp3 * N2c ^ 2 * s2v + Mp4 * N2c * s3v) * f := by
      ring
    rw [expand, hz1, hz0, zero_mul, zero_mul, add_zero]
  exact mul_left_cancel₀ (pow_ne_zero 4 N2c_ne_zero) (by rw [key, mul_zero])

/-! ## 5. `Σ_j Mp_j·dF_j = 0` and the conclusion -/

lemma dF_split (j : ℕ) :
    dF j = (Dx^[j]) HA + (Dx^[j]) (HA.subst sympPhi) := by
  rw [dF, ← Dx_iterate j (Ffun 0), Ffun_zero, HAF]
  induction j with
  | zero => simp only [Function.iterate_zero_apply, add_zero]
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih, Dx_add]

/-- **the bridge, reduced**: the cleared pull-back of the paper's operator
vanishes on `F₀⁽ʲ⁾` -/
lemma Mp_sum_zero : Mp0 * dF 0 + Mp1 * dF 1 + Mp2 * dF 2 + Mp3 * dF 3 + Mp4 * dF 4 = 0 := by
  have h0 : dF 0 = HA + HA.subst sympPhi := by
    rw [dF_split 0]; simp only [Function.iterate_zero_apply]
  have h1 : dF 1 = Dx HA + Dx (HA.subst sympPhi) := by
    rw [dF_split 1]; simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  have h2 : dF 2 = Dx (Dx HA) + Dx (Dx (HA.subst sympPhi)) := by
    rw [dF_split 2]
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  have h3 : dF 3 = Dx (Dx (Dx HA)) + Dx (Dx (Dx (HA.subst sympPhi))) := by
    rw [dF_split 3]
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  have h4 : dF 4 = Dx (Dx (Dx (Dx HA))) + Dx (Dx (Dx (Dx (HA.subst sympPhi)))) := by
    rw [dF_split 4]
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [h0, h1, h2, h3, h4]
  have hu := reduce_u HA u_ode
  have hv := reduce_v (HA.subst sympPhi) v_ode
  linear_combination hu + hv

/-- **the paper's eq. `(explicitode)`**: the symmetrized Hauptmodul series
`G_A(y) = Sym⁺H_A` satisfies the order-4 ODE with the paper's multipliers -/
theorem GA_odeLHS_eq_zero : GA_odeLHS = 0 := by
  have h1 : ((X : PowerSeries ℚ) - 1) ^ 19 * Yp ^ 7 * (GA_odeLHS.subst sympY) = 0 := by
    rw [cleared_pullback, Mp_sum_zero]
  have h2 : GA_odeLHS.subst sympY = 0 :=
    mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 19 XsubOne_ne_zero) (pow_ne_zero 7 Yp_ne_zero))
      (by rw [h1, mul_zero])
  exact symp_subst_y_injective GA_odeLHS h2

end Submission.CDT
