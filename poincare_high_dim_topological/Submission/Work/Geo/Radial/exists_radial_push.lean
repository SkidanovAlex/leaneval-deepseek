import Mathlib
import Submission.Work.Geo.Radial.Basic
import Submission.Work.Geo.Radial.RadialDefs
import Submission.Work.Geo.Radial.radRho_continuous
import Submission.Work.Geo.Radial.radRho_facts
import Submission.Work.Geo.Radial.radStretch_strictMono
import Submission.Work.Geo.Radial.radStretch_surjective
import Submission.Work.Geo.Radial.radStretchInv_facts
import Submission.Work.Geo.Radial.radPush_continuous
import Submission.Work.Geo.Radial.radPushInv_continuous

namespace Work.Geo.Radial

open Set Metric
open Work.Geo.Radial

set_option maxHeartbeats 1000000

/-! ### Elementary facts about `radPush` and `radPushInv` -/

/-- Membership in a cube centred at `q`, translated to the cube at the origin. -/
theorem mem_ocubeAround_sub {n : ℕ} [NeZero n] (q : PL.E n) (r : ℝ) (y : PL.E n) :
    y ∈ ocubeAround q r ↔ y - q ∈ ocubeAround (0 : PL.E n) r := by
  simp [ocubeAround]

/-- At `s = 0` the radial push is the identity. -/
theorem rp_zero_s {n : ℕ} [NeZero n] (ε R S : ℝ) (x : PL.E n) :
    radPush ε R S 0 x = x := by
  obtain ⟨hρnn, hρle, hρzero, hρsmul, -, -⟩ := radRho_facts (n := n)
  rcases eq_or_ne x 0 with rfl | hx
  · rw [radPush, (hρzero 0).mpr rfl, radStretch_at_zero]
    simp
  · rw [radPush, radStretch_zero_s, div_self (fun h => hx ((hρzero x).mp h)), one_smul]

/-- The radial push fixes the centre. -/
theorem rp_zero {n : ℕ} [NeZero n] (ε R S s : ℝ) :
    radPush ε R S s (0 : PL.E n) = 0 := by
  obtain ⟨-, -, hρzero, -, -, -⟩ := radRho_facts (n := n)
  rw [radPush, (hρzero 0).mpr rfl, radStretch_at_zero]
  simp

/-- The inverse radial push fixes the centre. -/
theorem rpinv_zero {n : ℕ} [NeZero n] (ε R S s : ℝ) :
    radPushInv ε R S s (0 : PL.E n) = 0 := by
  obtain ⟨-, -, hρzero, -, -, -⟩ := radRho_facts (n := n)
  rw [radPushInv, (hρzero 0).mpr rfl]
  simp

/-- The sup-norm radius of the radial push. -/
theorem rp_radRho {n : ℕ} [NeZero n] {ε R S s : ℝ} (hs : 0 ≤ s) (hεR : ε ≤ R)
    (x : PL.E n) : radRho (radPush ε R S s x) = radStretch ε R S s (radRho x) := by
  obtain ⟨hρnn, hρle, hρzero, hρsmul, -, -⟩ := radRho_facts (n := n)
  have hc : 0 ≤ radStretch ε R S s (radRho x) / radRho x :=
    div_nonneg (le_trans (hρnn x) (radStretch_ge_self hs hεR)) (hρnn x)
  rw [radPush, hρsmul _ _ hc]
  rcases eq_or_ne (radRho x) 0 with h | h
  · rw [h, mul_zero, radStretch_at_zero]
  · rw [div_mul_cancel₀ _ h]

/-- The sup-norm radius of the inverse radial push. -/
theorem rpinv_radRho {n : ℕ} [NeZero n] {ε R S s : ℝ} (hε : 0 < ε) (hεR : ε ≤ R)
    (hεS : ε < S) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hmono : StrictMono (radStretch ε R S s))
    (hsurj : Function.Surjective (radStretch ε R S s)) (y : PL.E n) :
    radRho (radPushInv ε R S s y) = radStretchInv ε R S s (radRho y) := by
  obtain ⟨hρnn, hρle, hρzero, hρsmul, -, -⟩ := radRho_facts (n := n)
  obtain ⟨hθφ, hφθ, hθcont, hθnn, hθle⟩ := radStretchInv_facts hε hεR hεS hs0 hs1 hmono hsurj
  have hθ0 : radStretchInv ε R S s 0 = 0 := by
    simpa [radStretch_at_zero] using hθφ (0 : ℝ)
  have hc : 0 ≤ radStretchInv ε R S s (radRho y) / radRho y :=
    div_nonneg (hθnn _ (hρnn y)) (hρnn y)
  rw [radPushInv, hρsmul _ _ hc]
  rcases eq_or_ne (radRho y) 0 with h | h
  · rw [h, hθ0, mul_zero]
  · rw [div_mul_cancel₀ _ h]

/-- `radPush` is the identity outside the cube of radius `S`. -/
theorem rp_of_ge {n : ℕ} [NeZero n] {ε R S s : ℝ} (hε : 0 < ε) (hεS : ε < S)
    {x : PL.E n} (hx : S ≤ radRho x) : radPush ε R S s x = x := by
  obtain ⟨hρnn, hρle, hρzero, hρsmul, -, -⟩ := radRho_facts (n := n)
  have hS0 : 0 < S := lt_trans hε hεS
  have hx0 : x ≠ 0 := fun h => by
    rw [h, (hρzero 0).mpr rfl] at hx
    linarith
  have ht : 0 < radRho x := lt_of_lt_of_le hS0 hx
  rw [radPush, radStretch_of_ge hεS hx, div_self (ne_of_gt ht), one_smul]

/-- At `s = 1` the radial push takes the cube of radius `ε` outside the cube of radius `R`. -/
theorem rp_one_eps {n : ℕ} [NeZero n] {ε R S : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hRS : R < S) {x : PL.E n} (hx : ε ≤ radRho x) :
    R ≤ radRho (radPush ε R S 1 x) := by
  obtain ⟨hρnn, hρle, hρzero, hρsmul, hρlt, hρle'⟩ := radRho_facts (n := n)
  have hεS : ε < S := lt_trans hεR hRS
  rw [rp_radRho (by norm_num : (0:ℝ) ≤ 1) (le_of_lt hεR)]
  calc R = radStretch ε R S 1 ε := (radStretch_eps hε hεS).symm
    _ ≤ radStretch ε R S 1 (radRho x) :=
        (radStretch_strictMono hε hεR hRS (by norm_num) (by norm_num)).monotone hx

/-- `radPushInv` is a left inverse of `radPush`. -/
theorem rp_leftInverse {n : ℕ} [NeZero n] {ε R S s : ℝ} (hε : 0 < ε) (hεR : ε ≤ R)
    (hεS : ε < S) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hmono : StrictMono (radStretch ε R S s))
    (hsurj : Function.Surjective (radStretch ε R S s)) :
    Function.LeftInverse (radPushInv (n := n) ε R S s) (radPush ε R S s) := by
  obtain ⟨hρnn, hρle, hρzero, hρsmul, -, -⟩ := radRho_facts (n := n)
  obtain ⟨hθφ, hφθ, hθcont, hθnn, hθle⟩ := radStretchInv_facts hε hεR hεS hs0 hs1 hmono hsurj
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · rw [rp_zero, rpinv_zero]
  · have ht : 0 < radRho x :=
      lt_of_le_of_ne (hρnn x) (Ne.symm (fun h => hx ((hρzero x).mp h)))
    have hu : 0 < radStretch ε R S s (radRho x) :=
      lt_of_lt_of_le ht (radStretch_ge_self hs0 hεR)
    have hkey : radRho x / radStretch ε R S s (radRho x) *
        (radStretch ε R S s (radRho x) / radRho x) = 1 := by
      rw [div_mul_div_comm, mul_comm (radStretch ε R S s (radRho x)) (radRho x),
        div_self (mul_ne_zero (ne_of_gt ht) (ne_of_gt hu))]
    rw [radPushInv, rp_radRho hs0 hεR x, hθφ (radRho x), radPush, smul_smul, hkey,
      one_smul]

/-- `radPushInv` is a right inverse of `radPush`. -/
theorem rp_rightInverse {n : ℕ} [NeZero n] {ε R S s : ℝ} (hε : 0 < ε) (hεR : ε ≤ R)
    (hεS : ε < S) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hmono : StrictMono (radStretch ε R S s))
    (hsurj : Function.Surjective (radStretch ε R S s)) :
    Function.RightInverse (radPushInv (n := n) ε R S s) (radPush ε R S s) := by
  obtain ⟨hρnn, hρle, hρzero, hρsmul, -, -⟩ := radRho_facts (n := n)
  obtain ⟨hθφ, hφθ, hθcont, hθnn, hθle⟩ := radStretchInv_facts hε hεR hεS hs0 hs1 hmono hsurj
  intro y
  rcases eq_or_ne y 0 with rfl | hy
  · rw [rpinv_zero, rp_zero]
  · have hu : 0 < radRho y :=
      lt_of_le_of_ne (hρnn y) (Ne.symm (fun h => hy ((hρzero y).mp h)))
    have htne : radStretchInv ε R S s (radRho y) ≠ 0 := by
      intro h
      have h0 : radRho y = 0 := by
        rw [← hφθ (radRho y), h, radStretch_at_zero]
      exact (ne_of_gt hu) h0
    have hkey : radRho y / radStretchInv ε R S s (radRho y) *
        (radStretchInv ε R S s (radRho y) / radRho y) = 1 := by
      rw [div_mul_div_comm,
        mul_comm (radStretchInv ε R S s (radRho y)) (radRho y),
        div_self (mul_ne_zero (ne_of_gt hu) htne)]
    rw [radPush, rpinv_radRho hε hεR hεS hs0 hs1 hmono hsurj y, hφθ (radRho y),
      radPushInv, smul_smul, hkey, one_smul]

/-- Continuity of the radial push at a fixed value of the parameter. -/
theorem rp_continuous_fixed {n : ℕ} [NeZero n] {ε R S : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hRS : R < S) (s : unitInterval) : Continuous (radPush (n := n) ε R S (s : ℝ)) := by
  have h2 : Continuous fun y : PL.E n => (s, y) :=
    continuous_const.prodMk (continuous_id : Continuous fun y : PL.E n => y)
  have h3 : Continuous fun y : PL.E n => radPush ε R S (s : ℝ) y :=
    (radPush_continuous (n := n) hε hεR hRS).comp h2
  exact h3

/-- Joint continuity of the translated radial push family. -/
theorem rp_conj_continuous {n : ℕ} [NeZero n] {ε R S : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hRS : R < S) (q : PL.E n) :
    Continuous fun p : unitInterval × PL.E n => q + radPush ε R S (p.1 : ℝ) (p.2 - q) := by
  have key : ∀ Ψ : unitInterval × PL.E n → PL.E n, Continuous Ψ →
      Continuous fun p : unitInterval × PL.E n => q + Ψ (p.1, p.2 - q) := by
    intro Ψ hΨ
    have hg : Continuous fun p : unitInterval × PL.E n => (p.1, p.2 - q) :=
      continuous_fst.prodMk (continuous_snd.sub continuous_const)
    exact continuous_const.add (hΨ.comp hg)
  exact key (fun z => radPush ε R S (z.1 : ℝ) z.2) (radPush_continuous (n := n) hε hεR hRS)

/-- The sup-norm radial push about `q` in `ℝⁿ`, as a continuous family of self-homeomorphisms
starting at the identity: `H s` fixes the complement of `ocubeAround q S` pointwise, keeps
`ocubeAround q S` inside itself, pushes (at `s = 1`) everything outside `ocubeAround q ε` outside
`ocubeAround q R`, and acts radially about `q` with a factor `≥ 1`.

The intended fully-qualified name is `Work.Geo.Radial.exists_radial_push` (file
`Submission/Work/Geo/Radial/exists_radial_push.lean`). -/
theorem exists_radial_push {n : ℕ} (q : EuclideanSpace ℝ (Fin n)) {ε R S : ℝ} (hε : 0 < ε)
    (hεR : ε < R) (hRS : R < S) :
    ∃ H : unitInterval → EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n),
      (Continuous fun p : unitInterval × EuclideanSpace ℝ (Fin n) => (H p.1) p.2) ∧
      H 0 = Homeomorph.refl (EuclideanSpace ℝ (Fin n)) ∧
      (∀ s y, y ∉ ocubeAround q S → (H s) y = y) ∧
      (∀ s y, y ∈ ocubeAround q S → (H s) y ∈ ocubeAround q S) ∧
      (∀ y, y ∉ ocubeAround q ε → (H 1) y ∉ ocubeAround q R) ∧
      (∀ s y, ∃ lam : ℝ, 1 ≤ lam ∧ ∀ i, (H s) y i - q i = lam * (y i - q i)) := by
  by_cases hn : n = 0
  · subst hn
    refine ⟨fun _ => Homeomorph.refl (PL.E 0), ?_, rfl, ?_, ?_, ?_, ?_⟩
    · simpa using (continuous_snd : Continuous fun p : unitInterval × PL.E 0 => p.2)
    · intro s y hy
      rfl
    · intro s y hy
      exact hy
    · intro y hy
      exact absurd (fun i : Fin 0 => Fin.elim0 i) hy
    · intro s y
      exact ⟨1, le_rfl, fun i => Fin.elim0 i⟩
  · haveI : NeZero n := ⟨hn⟩
    have hεS : ε < S := lt_trans hεR hRS
    have hεRle : ε ≤ R := le_of_lt hεR
    obtain ⟨hρnn, hρle, hρzero, hρsmul, hρlt, hρle'⟩ := radRho_facts (n := n)
    let Hf : unitInterval → PL.E n ≃ₜ PL.E n := fun s =>
      { toFun := fun y => q + radPush ε R S (s : ℝ) (y - q)
        invFun := fun y => q + radPushInv ε R S (s : ℝ) (y - q)
        left_inv := fun y => by
          show q + radPushInv ε R S (s : ℝ) (q + radPush ε R S (s : ℝ) (y - q) - q) = y
          rw [add_sub_cancel_left,
            rp_leftInverse hε hεRle hεS s.2.1 s.2.2
              (radStretch_strictMono hε hεR hRS s.2.1 s.2.2)
              (radStretch_surjective hε hεR hRS s.2.1 s.2.2) (y - q),
            add_sub_cancel]
        right_inv := fun y => by
          show q + radPush ε R S (s : ℝ) (q + radPushInv ε R S (s : ℝ) (y - q) - q) = y
          rw [add_sub_cancel_left,
            rp_rightInverse hε hεRle hεS s.2.1 s.2.2
              (radStretch_strictMono hε hεR hRS s.2.1 s.2.2)
              (radStretch_surjective hε hεR hRS s.2.1 s.2.2) (y - q),
            add_sub_cancel]
        continuous_toFun := by
          have h1 : Continuous fun y : PL.E n => radPush ε R S (s : ℝ) y :=
            rp_continuous_fixed hε hεR hRS s
          have h2 : Continuous fun y : PL.E n => y - q :=
            continuous_id.sub continuous_const
          exact continuous_const.add (h1.comp h2)
        continuous_invFun := by
          have h1 : Continuous fun y : PL.E n => radPushInv ε R S (s : ℝ) y :=
            radPushInv_continuous hε hεRle hεS s.2.1 s.2.2
              (radStretch_strictMono hε hεR hRS s.2.1 s.2.2)
              (radStretch_surjective hε hεR hRS s.2.1 s.2.2)
          have h2 : Continuous fun y : PL.E n => y - q :=
            continuous_id.sub continuous_const
          exact continuous_const.add (h1.comp h2) }
    have hH : ∀ (s : unitInterval) (y : PL.E n),
        (Hf s) y = q + radPush ε R S (s : ℝ) (y - q) := fun s y => rfl
    refine ⟨Hf, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- joint continuity
      rw [show (fun p : unitInterval × PL.E n => (Hf p.1) p.2)
            = fun p : unitInterval × PL.E n => q + radPush ε R S (p.1 : ℝ) (p.2 - q)
          from funext fun p => hH p.1 p.2]
      exact rp_conj_continuous hε hεR hRS q
    · -- `H 0` is the identity
      refine Homeomorph.ext fun y => ?_
      rw [hH 0 y, Homeomorph.refl_apply]
      show q + radPush ε R S (0 : ℝ) (y - q) = y
      rw [rp_zero_s, add_sub_cancel]
    · -- `H s` fixes the complement of the cube of radius `S`
      intro s y hy
      rw [hH s y]
      have hy' : y - q ∉ ocubeAround (0 : PL.E n) S :=
        fun h => hy ((mem_ocubeAround_sub q S y).mpr h)
      have hS : S ≤ radRho (y - q) := not_lt.mp fun h => hy' ((hρlt (y - q) S).mp h)
      rw [rp_of_ge hε hεS hS, add_sub_cancel]
    · -- `H s` keeps the cube of radius `S` inside itself
      intro s y hy
      rw [hH s y]
      have hy' : y - q ∈ ocubeAround (0 : PL.E n) S := (mem_ocubeAround_sub q S y).mp hy
      have htS : radRho (y - q) < S := (hρlt (y - q) S).mpr hy'
      have h2 : radStretch ε R S (s : ℝ) (radRho (y - q)) < S := by
        have h3 := (radStretch_strictMono hε hεR hRS s.2.1 s.2.2).lt_iff_lt.mpr htS
        rwa [radStretch_S hεS] at h3
      rw [mem_ocubeAround]
      intro i
      have hi : (q + radPush ε R S (s : ℝ) (y - q)) i - q i
          = radPush ε R S (s : ℝ) (y - q) i := by simp
      rw [hi]
      calc |radPush ε R S (s : ℝ) (y - q) i|
          ≤ radRho (radPush ε R S (s : ℝ) (y - q)) := hρle _ i
        _ = radStretch ε R S (s : ℝ) (radRho (y - q)) := rp_radRho s.2.1 hεRle (y - q)
        _ < S := h2
    · -- at `s = 1`, everything outside the `ε`-cube leaves the `R`-cube
      intro y hy
      rw [hH 1 y]
      have hy' : y - q ∉ ocubeAround (0 : PL.E n) ε :=
        fun h => hy ((mem_ocubeAround_sub q ε y).mpr h)
      have hεle : ε ≤ radRho (y - q) := not_lt.mp fun h => hy' ((hρlt (y - q) ε).mp h)
      intro hyR
      have hyR' : (q + radPush ε R S ((1 : unitInterval) : ℝ) (y - q)) - q
          ∈ ocubeAround (0 : PL.E n) R := (mem_ocubeAround_sub q R _).mp hyR
      have hsub : (q + radPush ε R S ((1 : unitInterval) : ℝ) (y - q)) - q
          = radPush ε R S 1 (y - q) := by
        rw [add_sub_cancel_left]
        rfl
      rw [hsub] at hyR'
      have hlt : radRho (radPush ε R S 1 (y - q)) < R := (hρlt _ R).mpr hyR'
      exact absurd hlt (not_lt.mpr (rp_one_eps hε hεR hRS hεle))
    · -- radiality
      intro s y
      by_cases hyq : y = q
      · refine ⟨1, le_rfl, ?_⟩
        intro i
        rw [hH s y]
        have hq : q + radPush ε R S (s : ℝ) (y - q) = q := by
          rw [hyq, sub_self, rp_zero, add_zero]
        rw [hq]
        simp [hyq]
      · have hxne : y - q ≠ 0 := sub_ne_zero.mpr hyq
        have ht : 0 < radRho (y - q) :=
          lt_of_le_of_ne (hρnn _) (Ne.symm (fun h => hxne ((hρzero _).mp h)))
        rw [hH s y]
        refine ⟨radStretch ε R S (s : ℝ) (radRho (y - q)) / radRho (y - q), ?_, ?_⟩
        · rw [le_div_iff₀ ht, one_mul]
          exact radStretch_ge_self s.2.1 hεRle
        · intro i
          rw [radPush]
          simp [add_sub_cancel_left]

end Work.Geo.Radial
