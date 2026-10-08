import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.GaloisField
import Submission.Work.PSU3.FMap
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Work.ThmF

namespace Work.PSU3.StageC

set_option maxHeartbeats 800000

/-- **The fine coordinates on `Q₀`.**  Once `e : Q ≃* SZ (E n)` has the `x`-coordinate
`(e x).x = μ · bar x` (formula C1), sends `s = zc 1` to `(0,1)` and is equivariant under the
torus action of `KW`, and once `nm` is the squaring map, `e` is forced on the whole copy
`zc(F) = Q₀` of the fixed field: `e (zc y) = (0, y)`.

The argument is purely formal.  Write `Φ w := (e (zc w)).y` for `w` fixed by `σE`.  From
`bar (zc w) = 1` (the `x`-coordinate vanishes) and `zc (w + w') = zc w · zc w'`, `Φ` is
additive, so `Φ 0 = 0` (characteristic two).  Applying `heq` to `d ∈ K` with `κ d = a` and
using `act_zc_K` gives `Φ (nm a · w) = (a · σ a) · Φ w`, i.e. `Φ (a² w) = a² Φ w` for every
fixed unit `a`.  Since squaring is a bijection of the (finite) fixed field, this is
`Φ (c w) = c Φ w` for all `c` in the fixed field, and `Φ 1 = 1` (from `hes`) forces `Φ = id`. -/
theorem e_zc_eq {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n)
    (hsq : ∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a →
      (fr.nm a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ 2)
    (e : Q ≃* SZ (Work.PSU3.E n)) (μ : (Work.PSU3.E n)ˣ)
    (hex : ∀ x : Q, (e x).x = (μ : Work.PSU3.E n) * Multiplicative.toAdd (fr.bar x))
    (hes : ∀ hs : fr.zc 1 ∈ Q, (e ⟨fr.zc 1, hs⟩).x = 0 ∧ (e ⟨fr.zc 1, hs⟩).y = 1)
    (heq : ∀ (d : fr.KW) (x y : Q), (y : G) = (d : G)⁻¹ * x * d →
      e y = SZ.torusAct (fr.κ d) (e x)) :
    ∀ (y : Work.PSU3.E n) (hy : σE y = y) (hQ : fr.zc y ∈ Q),
      (e ⟨fr.zc y, hQ⟩).x = 0 ∧ (e ⟨fr.zc y, hQ⟩).y = y := by
  classical
  intro y hy hQ
  have _ := hS
  -- the element of `Q` attached to a fixed field element
  let zcQ : (w : E n) → σE w = w → Q :=
    fun w hw => ⟨fr.zc w, fr.Q0_le (fr.zc_mem w hw)⟩
  -- the `x`-coordinate vanishes, because `zc w ∈ Q₀ = ker bar`
  have hx0 : ∀ (w : E n) (hw : σE w = w), (e (zcQ w hw)).x = 0 := by
    intro w hw
    have hbar : fr.bar (zcQ w hw) = 1 := (fr.bar_eq_one_iff _).mpr (fr.zc_mem w hw)
    rw [hex (zcQ w hw), hbar]
    simp
  -- the `y`-coordinate of `e` on `zc (F)`, as a plain function of `E n`
  let Φ : E n → E n := fun w => if h : σE w = w then (e (zcQ w h)).y else 0
  have hΦ : ∀ (w : E n) (hw : σE w = w), Φ w = (e (zcQ w hw)).y := by
    intro w hw
    simp only [Φ]
    rw [dite_eq_left hw]
  have hσ1 : σE (1 : E n) = 1 := map_one _
  -- additivity of `Φ`
  have hΦadd : ∀ (w w' : E n) (hw : σE w = w) (hw' : σE w' = w'),
      Φ (w + w') = Φ w + Φ w' := by
    intro w w' hw hw'
    have hww' : σE (w + w') = w + w' := by rw [map_add, hw, hw']
    rw [hΦ (w + w') hww', hΦ w hw, hΦ w' hw']
    have hQeq : zcQ (w + w') hww' = zcQ w hw * zcQ w' hw' := by
      apply Subtype.ext
      show fr.zc (w + w') = fr.zc w * fr.zc w'
      exact fr.zc_add w w' hw hw'
    have hmul : e (zcQ (w + w') hww') = e (zcQ w hw) * e (zcQ w' hw') := by
      rw [hQeq, map_mul]
    rw [hmul, SZ.mul_y, hx0 w hw, hx0 w' hw']
    simp
  have hΦ1 : Φ 1 = 1 := by
    rw [hΦ 1 hσ1]
    exact (hes (fr.Q0_le (fr.zc_mem 1 hσ1))).2
  have hΦ0 : Φ 0 = 0 := by
    have h11 : (1 : E n) + 1 = 0 := by
      rw [one_add_one_eq_two, CharTwo.two_eq_zero]
    calc Φ 0 = Φ ((1 : E n) + 1) := by rw [h11]
      _ = Φ 1 + Φ 1 := hΦadd 1 1 hσ1 hσ1
      _ = 0 := by rw [hΦ1, h11]
  -- equivariance of `Φ` against the torus action of `K`: `Φ (a² w) = a² Φ w`
  have hΦsq : ∀ (c : (E n)ˣ) (hc : σE (c : E n) = (c : E n))
      (w : E n) (hw : σE w = w), Φ ((c : E n) ^ 2 * w) = (c : E n) ^ 2 * Φ w := by
    intro c hc w hw
    obtain ⟨d, hd⟩ := fr.K_surj c hc
    have hκfix : σE ((fr.κ d : (E n)ˣ) : E n) = ((fr.κ d : (E n)ˣ) : E n) := by
      rw [hd]; exact hc
    have hdK : (d : G) ∈ Ksub H t := (fr.mem_K_iff d).mpr hκfix
    have hnmfix : σE ((fr.nm (fr.κ d) : (E n)ˣ) : E n)
        = ((fr.nm (fr.κ d) : (E n)ˣ) : E n) :=
      fr.nm_F (fr.κ d) hκfix
    have harg : σE ((fr.nm (fr.κ d) : E n) * w) = (fr.nm (fr.κ d) : E n) * w := by
      rw [map_mul, hnmfix, hw]
    have hmemb : ((zcQ ((fr.nm (fr.κ d) : E n) * w) harg : Q) : G)
        = (d : G)⁻¹ * (zcQ w hw : G) * d := by
      show fr.zc ((fr.nm (fr.κ d) : E n) * w) = (d : G)⁻¹ * fr.zc w * d
      exact (fr.act_zc_K d hdK w hw).symm
    have hheq := heq d (zcQ w hw) (zcQ ((fr.nm (fr.κ d) : E n) * w) harg) hmemb
    have hy2 := congrArg (fun z : SZ (E n) => z.y) hheq
    simp only [SZ.torusAct_y] at hy2
    rw [← hΦ ((fr.nm (fr.κ d) : E n) * w) harg, ← hΦ w hw] at hy2
    have hnm_eq : (fr.nm (fr.κ d) : E n) = (c : E n) ^ 2 := by
      rw [hd]; exact hsq c hc
    have hcoef : ((fr.κ d : (E n)ˣ) : E n) * σE (((fr.κ d : (E n)ˣ) : E n))
        = (c : E n) ^ 2 := by
      rw [hd, hc, pow_two]
    rw [hnm_eq, hcoef] at hy2
    exact hy2
  -- squaring is a bijection of the (finite) fixed field
  have hsqrt : ∀ c : E n, σE c = c → ∃ b : E n, σE b = b ∧ b ^ 2 = c := by
    intro c hc
    let Fix := {x : E n // σE x = x}
    haveI : Finite Fix := inferInstance
    let φ : Fix → Fix := fun x => ⟨x.1 ^ 2, by rw [map_pow, x.2]⟩
    have hinj : Function.Injective φ := by
      intro a b hab
      have hval : a.1 ^ 2 = b.1 ^ 2 := congrArg Subtype.val hab
      have hab' : a.1 = b.1 := by
        have h2 : (a.1 + b.1) * (a.1 + b.1) = 0 := by
          rw [← pow_two, CharTwo.add_sq, hval]
          exact CharTwo.add_self_eq_zero _
        have h3 : a.1 + b.1 = 0 := mul_self_eq_zero.mp h2
        rw [eq_neg_of_add_eq_zero_left h3, CharTwo.neg_eq]
      exact Subtype.ext hab'
    have hsurj : Function.Surjective φ := (Finite.injective_iff_surjective).mp hinj
    obtain ⟨b, hb⟩ := hsurj ⟨c, hc⟩
    exact ⟨b.1, b.2, congrArg Subtype.val hb⟩
  -- `Φ` is linear over the fixed field
  have hΦlin : ∀ (c : E n) (hc : σE c = c) (w : E n) (hw : σE w = w),
      Φ (c * w) = c * Φ w := by
    intro c hc w hw
    by_cases hc0 : c = 0
    · rw [hc0, zero_mul, zero_mul]
      exact hΦ0
    · obtain ⟨b, hb, hb2⟩ := hsqrt c hc
      have hb0 : b ≠ 0 := by
        intro hb0'
        apply hc0
        rw [← hb2, hb0']
        ring
      have hbu : σE ((Units.mk0 b hb0 : (E n)ˣ) : E n)
          = ((Units.mk0 b hb0 : (E n)ˣ) : E n) := hb
      have hkey := hΦsq (Units.mk0 b hb0) hbu w hw
      simp only [Units.val_mk0] at hkey
      rw [hb2] at hkey
      exact hkey
  have hσy1 : σE (y * 1) = y * 1 := by rw [mul_one, hy]
  have key := hΦlin y hy 1 hσ1
  rw [mul_one] at key
  rw [hΦ1, mul_one] at key
  have hsub : (⟨fr.zc y, hQ⟩ : Q) = zcQ y hy := Subtype.ext rfl
  refine ⟨?_, ?_⟩
  · rw [hsub]
    exact hx0 y hy
  · rw [hsub]
    calc (e (zcQ y hy)).y = Φ y := (hΦ y hy).symm
      _ = y := key

end Work.PSU3.StageC
