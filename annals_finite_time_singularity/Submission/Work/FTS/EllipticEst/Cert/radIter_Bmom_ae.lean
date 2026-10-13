/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `D_z`-iterates of the angular moment are the radial moments

`Bmom F j z = ∫_θ D_z^j F(z,θ)·sinθcos²θ dθ` (`Work.FTS.EllipticEst.Bmom`,
`Work.FTS.EllipticEst.PsiInt`) is the `j`-th radial moment of the source `F`.  The
certificate `Work.FTS.EllipticEst.Cert.HkMem_Fstar_sin` needs the identity

  `radIter (Bmom F 0) j z = Bmom F j z`   for `j ≤ k` and almost every `z > 0`,

i.e. that the `j`-th `D_z`-iterate of the angular moment `F_*(F)` — the radial coefficient
of the separated function `F_*(F)(z)·sin 2θ` — is the moment `Bmom F j`.

## Proof

`D_z = z ∂_z` (`Work.Spaces.Dz`, `Work.Spaces.DzIter_succ`), so the moments form a *tower*:
for `0 < s ≤ z`

  `B_j(z) - B_j(s) = ∫_s^z B_{j+1}(r)/r dr`      (`radIter_bmom_chain`),

which is `FstarDzIter_chain_open` (of `Cert/GbarSin/FstarDzIter_chain_open.lean`, itself
`sorry`-free) rewritten through `Bmom_eq_Fstar_DzIter`.  Consequences:

* `B_j` is continuous on `(0,∞)` for `j + 1 ≤ k`, being a primitive of the locally
  integrable function `B_{j+1}(s)/s` (`radIter_bmom_continuousOn`);
* hence `B_{j+1}(s)/s` is *continuous* on `(0,∞)`, and the fundamental theorem of calculus
  gives `HasDerivAt (B_j) (B_{j+1} z / z) z` **everywhere** on `(0,∞)` as soon as
  `j + 2 ≤ k` (`radIter_bmom_hasDerivAt`);
* at the top level `j = k - 1` only `j + 1 ≤ k` is available, so the Lebesgue
  differentiation theorem (`IntervalIntegrable.ae_hasDerivAt_integral`, applied on a
  countable family of intervals covering `(0,∞)`) gives the same statement *almost
  everywhere* (`radIter_bmom_ae_hasDerivAt`).

The identity itself follows by induction on `j` for `j + 1 ≤ k`
(`radIter_bmom_eq_all`: `radIter (B_0) j = B_j` everywhere on `(0,∞)`), while the top
iterate `j = k` is handled by the a.e. derivative (`radIter_bmom_ae_top`).  The target
`radIter_Bmom_ae` is exactly the combination of the two, the case `j = k` being the only
one not covered by the everywhere statement.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.OpenQAux
import Submission.Work.FTS.EllipticEst.OpenQAng
import Submission.Work.FTS.EllipticEst.integrableOn_slice_l2
import Submission.Work.FTS.EllipticEst.integrableOn_box_of_slice
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.PsiInt_sq_mul_w_le_open
import Submission.Work.FTS.EllipticEst.FstarDzIter_sq_mul_w_le_open
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.FstarDzIter_chain_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {F : ℝ → ℝ → ℝ}

/-! ## The moment tower

`B_{j+1}(s)/s` is the derivative of `B_j`; this is the *only* analytic input of the
identity, and it is available `sorry`-free as `FstarDzIter_chain_open`. -/

/-- **The moment tower** (difference form).  For `0 < s ≤ z` and `j + 1 ≤ k`,
`B_j(z) - B_j(s) = ∫_s^z B_{j+1}(r)/r dr`. -/
theorem radIter_bmom_chain (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 1 ≤ k) {s z : ℝ} (hs : 0 < s)
    (hsz : s ≤ z) :
    Bmom F j z - Bmom F j s = ∫ r in s..z, Bmom F (j + 1) r / r := by
  simpa only [Bmom_eq_Fstar_DzIter] using
    GbarSin.FstarDzIter_chain_open α k F hF hmem j hj hs hsz

/-- **The moment tower** (anchored form): for `0 < a < b` and `j + 1 ≤ k`,
`B_j(b) = B_j(a) + ∫_a^b B_{j+1}(s)/s ds`. -/
theorem radIter_bmom_relation (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 1 ≤ k) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) :
    Bmom F j b = Bmom F j a + ∫ s in a..b, Bmom F (j + 1) s / s := by
  have h := radIter_bmom_chain α k hF hmem j hj ha hab.le
  linarith

/-- **The moment tower anchored at `c`**: for every `y > 0`,
`B_j(y) = B_j(c) + ∫_c^y B_{j+1}(s)/s ds`. -/
theorem radIter_bmom_eq_const_add_integral (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 1 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∀ y : ℝ, 0 < y → Bmom F j y = Bmom F j c + ∫ s in c..y, Bmom F (j + 1) s / s := by
  intro y hy
  rcases lt_trichotomy y c with hlt | heq | hgt
  · have hrel := radIter_bmom_relation α k hF hmem j hj hy hlt
    rw [hrel, intervalIntegral.integral_symm]
    ring
  · subst heq
    simp
  · exact radIter_bmom_relation α k hF hmem j hj hc hgt

/-! ## Continuity of the moments -/

/-- The `j`-th moment is continuous on `(0,∞)`, for `j + 1 ≤ k`. -/
theorem radIter_bmom_continuousOn (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 1 ≤ k) :
    ContinuousOn (fun z => Bmom F j z) (Set.Ioi 0) := by
  intro z hz
  have hz0 : 0 < z := hz
  set a : ℝ := z / 2 with ha_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have haz : a < z := by rw [ha_def]; linarith
  have hb : a < z + a := by linarith
  have hg : IntegrableOn (fun s => Bmom F (j + 1) s / s) (Set.uIcc a (z + a)) := by
    rw [Set.uIcc_of_le hb.le]
    exact integrableOn_Bmom_div α k hF hmem (j + 1) (by omega) a (z + a) ha0 hb
  have hΦ : ContinuousOn (fun x : ℝ => ∫ s in a..x, Bmom F (j + 1) s / s)
      (Set.uIcc a (z + a)) :=
    intervalIntegral.continuousOn_primitive_interval hg
  have hU : Set.uIcc a (z + a) ∈ 𝓝 z := by
    rw [Set.uIcc_of_le hb.le]
    exact Icc_mem_nhds haz (by linarith)
  have hcontΦ : ContinuousWithinAt (fun x : ℝ => ∫ s in a..x, Bmom F (j + 1) s / s)
      (Set.Ioi 0) z :=
    (hΦ.continuousAt hU).continuousWithinAt
  have hev : (fun x : ℝ => Bmom F j x) =ᶠ[𝓝[Set.Ioi 0] z]
      (fun x : ℝ => Bmom F j a + ∫ s in a..x, Bmom F (j + 1) s / s) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact radIter_bmom_eq_const_add_integral α k hF hmem j hj ha0 x hx
  have hz_e : Bmom F j z = Bmom F j a + ∫ s in a..z, Bmom F (j + 1) s / s :=
    radIter_bmom_eq_const_add_integral α k hF hmem j hj ha0 z hz0
  exact (continuousWithinAt_const.add hcontΦ).congr_of_eventuallyEq hev hz_e

/-! ## Differentiability of the moments -/

/-- **The `j`-th moment is differentiable everywhere on `(0,∞)`** with derivative
`B_{j+1}(z)/z`, as soon as `j + 2 ≤ k` (so that `B_{j+1}` — and hence `B_{j+1}(s)/s` — is
continuous, which makes the fundamental theorem of calculus available). -/
theorem radIter_bmom_hasDerivAt (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 2 ≤ k) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z => Bmom F j z) (Bmom F (j + 1) z / z) z := by
  have hz0 : 0 < z := hz
  set a : ℝ := z / 2 with ha_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have haz : a < z := by rw [ha_def]; linarith
  have hcontOn : ContinuousOn (fun s : ℝ => Bmom F (j + 1) s / s) (Set.Ioi 0) :=
    (radIter_bmom_continuousOn α k hF hmem (j + 1) (by omega)).div continuousOn_id
      (fun s hs => (show (0 : ℝ) < s from hs).ne')
  have hcont : ContinuousAt (fun s : ℝ => Bmom F (j + 1) s / s) z :=
    hcontOn.continuousAt (isOpen_Ioi.mem_nhds hz0)
  have hInt : IntervalIntegrable (fun s : ℝ => Bmom F (j + 1) s / s) volume a z := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le haz.le]
    exact integrableOn_Bmom_div α k hF hmem (j + 1) (by omega) a z ha0 haz
  have hder := intervalIntegral.integral_hasDerivAt_right hInt
    (hcontOn.stronglyMeasurableAtFilter isOpen_Ioi z hz0) hcont
  have hev : (fun x : ℝ => Bmom F j x) =ᶠ[𝓝 z]
      (fun x : ℝ => Bmom F j a + ∫ s in a..x, Bmom F (j + 1) s / s) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz0] with x hx
    exact radIter_bmom_eq_const_add_integral α k hF hmem j (by omega) ha0 x hx
  exact hev.hasDerivAt_iff.mpr (hder.const_add (Bmom F j a))

/-- **A.e. differentiability of the top moment.**  For `k ≥ 1`, for almost every `z > 0` the
moment `B_{k-1}` is differentiable at `z` with derivative `B_k(z)/z`.  Only `k ≤ k` is
available for the tower, so this is the Lebesgue differentiation theorem
(`IntervalIntegrable.ae_hasDerivAt_integral`) applied on the countable family of intervals
`[1/(n+1), n+2]` covering `(0,∞)`. -/
theorem radIter_bmom_ae_hasDerivAt (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (hk : 1 ≤ k) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      HasDerivAt (fun z => Bmom F (k - 1) z) (Bmom F k z / z) z := by
  set P : ℝ → Prop := fun x => HasDerivAt (fun x => Bmom F (k - 1) x) (Bmom F k x / x) x
    with hP
  have key : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2))),
      P x := by
    intro n
    set a : ℝ := 1 / ((n : ℝ) + 1) with hadef
    set b : ℝ := (n : ℝ) + 2 with hbdef
    have hpos : 0 < a := by rw [hadef]; positivity
    have hlt : a < b := by
      have hbpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [hadef, hbdef, div_lt_iff₀ hbpos]
      nlinarith
    have hle : a ≤ b := hlt.le
    have hInt : IntervalIntegrable (fun s : ℝ => Bmom F k s / s) volume a b := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
      exact integrableOn_Bmom_div α k hF hmem k le_rfl a b hpos hlt
    have hldt := IntervalIntegrable.ae_hasDerivAt_integral hInt
    rw [Set.uIcc_of_le hle] at hldt
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hldt] with x hx
    intro hxmem
    have hxpos : 0 < x := lt_of_lt_of_le hpos hxmem.1
    have hder : HasDerivAt (fun y => ∫ t in a..y, Bmom F k t / t) (Bmom F k x / x) x :=
      hx hxmem a ⟨le_rfl, hle⟩
    have hev : (fun y => Bmom F (k - 1) y) =ᶠ[𝓝 x]
        (fun y => Bmom F (k - 1) a + ∫ t in a..y, Bmom F k t / t) := by
      filter_upwards [isOpen_Ioi.mem_nhds hxpos] with y hy
      have h := radIter_bmom_eq_const_add_integral α k hF hmem (k - 1) (by omega) hpos y hy
      rw [show (k - 1) + 1 = k from by omega] at h
      exact h
    exact hev.hasDerivAt_iff.mpr (hder.const_add _)
  have keynull : ∀ n : ℕ, volume {x | x ∈ Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2)
      ∧ ¬ P x} = 0 := by
    intro n
    have h := key n
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff] at h
    have hset : {x | x ∈ Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) ∧ ¬ P x}
        = {x | ¬ (x ∈ Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) → P x)} := by
      ext x
      simp only [Set.mem_setOf_eq, not_imp]
    rw [hset]
    exact h
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi, MeasureTheory.ae_iff]
  refine measure_mono_null ?_ (measure_iUnion_null keynull)
  intro x hx
  have hx' : x ∈ Set.Ioi 0 ∧ ¬ P x := by
    simpa only [Set.mem_setOf_eq, not_imp] using hx
  obtain ⟨hx0, hxn⟩ := hx'
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ,
      1 / ((n : ℝ) + 1) ≤ x ∧ x ≤ (n : ℝ) + 2 := by
    obtain ⟨n, hn⟩ := exists_nat_ge (max x (1 / x))
    refine ⟨n, ?_, ?_⟩
    · have hx1 : 1 / x ≤ (n : ℝ) := le_trans (le_max_right _ _) hn
      have : 1 ≤ x * (n : ℝ) := by
        rw [div_le_iff₀ hx0] at hx1
        linarith
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      nlinarith
    · have hxn' : x ≤ (n : ℝ) := le_trans (le_max_left _ _) hn
      linarith
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  show x ∈ Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) ∧ ¬ P x
  exact ⟨⟨hn1, hn2⟩, hxn⟩

/-! ## The identity `(D_z^j F_*)(z) = B_j(z)` -/

/-- **The `D_z`-iterates of the angular moment are the moments** (everywhere on `(0,∞)`,
for all `j` with `j + 1 ≤ k`). -/
theorem radIter_bmom_eq_all (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) :
    ∀ j : ℕ, j + 1 ≤ k → ∀ z : ℝ, 0 < z →
      radIter (fun z => Bmom F 0 z) j z = Bmom F j z := by
  intro j
  induction j with
  | zero => intro _ z _; rfl
  | succ n ih =>
      intro hj z hz
      rw [radIter_succ]
      have hev : (radIter (fun z => Bmom F 0 z) n) =ᶠ[𝓝 z] (fun z => Bmom F n z) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih (by omega) z' hz'
      rw [hev.deriv_eq, (radIter_bmom_hasDerivAt α k hF hmem n (by omega) hz).deriv]
      rw [mul_div_assoc', mul_div_cancel_left₀ _ hz.ne']

/-- **The top `D_z`-iterate**, almost everywhere: for `k ≥ 1` and almost every `z > 0`,
`radIter (B_0) k z = B_k z`. -/
theorem radIter_bmom_ae_top (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (hk : 1 ≤ k) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      radIter (fun z => Bmom F 0 z) k z = Bmom F k z := by
  have h1 := radIter_bmom_ae_hasDerivAt α k hF hmem hk
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at h1
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [h1] with z hzimp
  intro hzmem
  have hz0 : 0 < z := hzmem
  have hk_eq : k = (k - 1) + 1 := by omega
  conv_lhs => rw [hk_eq]
  rw [radIter_succ]
  have hev : (radIter (fun z => Bmom F 0 z) (k - 1)) =ᶠ[𝓝 z]
      (fun z => Bmom F (k - 1) z) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz0] with z' hz'
    exact radIter_bmom_eq_all α k hF hmem (k - 1) (by omega) z' hz'
  rw [hev.deriv_eq, (hzimp hzmem).deriv]
  rw [mul_div_assoc', mul_div_cancel_left₀ _ hz0.ne']

/-! ## The target -/

/-- **The `D_z`-iterates of the angular moment are the radial moments, a.e.**  For a source
`F` which is `C^∞` on the open quadrant and honestly in `ℋ^k`, for almost every `z > 0` and
every `j ≤ k`,

  `radIter (Bmom F 0) j z = Bmom F j z`.

This is the separation identity used by `Cert.HkMem_Fstar_sin`: it identifies the radial
coefficients of `D_z^j (F_*(F)·sin 2θ)` — hence the `ℋ^k`-integrand of `F_*(F)·sin 2θ`
(`Cert.HkIntegrand_radial_sin`) — with the moments `F_*(D_z^j F)` of the source. -/
theorem radIter_Bmom_ae (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ∀ j : ℕ, j ≤ k →
        Work.FTS.EllipticEst.radIter (fun z => Work.FTS.EllipticEst.Bmom F 0 z) j z
          = Work.FTS.EllipticEst.Bmom F j z := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk]
    filter_upwards with z
    intro j hj
    have hj0 : j = 0 := Nat.le_zero.mp hj
    rw [hj0]
    rfl
  · have htop := radIter_bmom_ae_top α k hF hmem hk
    filter_upwards [htop, self_mem_ae_restrict measurableSet_Ioi] with z htopz hz
    intro j hj
    rcases lt_or_eq_of_le hj with hlt | heq
    · exact radIter_bmom_eq_all α k hF hmem j (by omega) z hz
    · subst heq
      exact htopz

end Work.FTS.EllipticEst.Cert
