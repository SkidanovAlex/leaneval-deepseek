import Mathlib
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.tpart_second_diff_pos

/-!
# A point with positive injectivity radius for a discrete subgroup of `PO(n,1)`

`Work.Mostow.exists_pos_le_dist`: if `Γ ≤ PO(n,1)` is discrete and nontrivial, then there is a
point `o` of hyperbolic space and `δ > 0` such that every `γ ≠ 1` in `Γ` displaces `o` by at
least `δ`:

`∃ o, ∃ δ > 0, ∀ γ ≠ 1, δ ≤ hdist o (γ • o)`.

The proof is the "generic point" argument, made quantitative.

* `F := {γ ∈ Γ | hdist 0 (γ • 0) ≤ 1}` is finite (`finite_nearStab`).
* A nontrivial isometry cannot fix a nonempty open set pointwise: a matrix which acts as a scalar
  on the hyperboloid lifts of the points of a ball is that scalar times the identity
  (`matrix_eq_smul_one_of_fixes_ball`, whose input is the strict convexity of `tpart` along a
  coordinate line, `tpart_second_diff_pos`).
* Hence the finite union of the fixed sets of the nontrivial elements of `F` misses a small ball
  around `0` (`exists_avoid_smul_finset`); any point `o` of that ball with `hdist 0 o < 1/4` which
  is not fixed by any nontrivial element of `F` works: for `γ ∈ F` the displacement at `o` is
  positive, while for `γ ∉ F` the displacement at `0` exceeds `1` and hence the displacement at
  `o` exceeds `1 - 2·(1/4) = 1/2`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open Matrix

noncomputable section

variable {n : ℕ}

/-! ## The rigidity input -/

/-- The difference of the hyperboloid lifts of two points, in terms of the unit `(inl i)` vector
and the time vector. -/
lemma hlift_shift_sub (u : E n) (i : Fin n) (ε : ℝ) :
    hlift (u + ε • EuclideanSpace.single i (1 : ℝ)) - hlift u
      = ε • (Pi.single (Sum.inl i) (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ)
        + (tpart (u + ε • EuclideanSpace.single i (1 : ℝ)) - tpart u)
          • (Pi.single (Sum.inr 0) (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ) := by
  funext b
  rcases b with j | k
  · simp only [Pi.sub_apply, hlift_inl, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, WithLp.ofLp_toLp, Pi.single_apply,
      Sum.inl.injEq, Pi.zero_apply, mul_zero, add_zero]
    by_cases h : j = i <;> simp [h]
  · obtain rfl : k = 0 := Subsingleton.elim _ _
    simp only [Pi.sub_apply, hlift_inr, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      Pi.add_apply, Pi.zero_apply, mul_zero, zero_add, Sum.inr.injEq, Sum.inr_ne_inl, reduceIte, mul_one]


/-- The second difference of the lifts along the `i`-th coordinate line is a multiple of the
`(inr 0)`-vector. -/
lemma hlift_shift_add (u : E n) (i : Fin n) (ε : ℝ) :
    (hlift (u + ε • EuclideanSpace.single i (1 : ℝ)) - hlift u)
      + (hlift (u - ε • EuclideanSpace.single i (1 : ℝ)) - hlift u)
      = (tpart (u + ε • EuclideanSpace.single i (1 : ℝ))
          + tpart (u - ε • EuclideanSpace.single i (1 : ℝ)) - 2 * tpart u)
        • (Pi.single (Sum.inr 0) (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ) := by
  funext b
  rcases b with j | k
  · simp only [Pi.add_apply, Pi.sub_apply, hlift_inl, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, Pi.zero_apply, mul_zero, PiLp.add_apply, PiLp.sub_apply,
      PiLp.smul_apply, WithLp.ofLp_toLp, Sum.inl_ne_inr, reduceIte]
    ring
  · obtain rfl : k = 0 := Subsingleton.elim _ _
    simp only [Pi.add_apply, Pi.sub_apply, hlift_inr, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, Sum.inr.injEq, reduceIte, mul_one]
    ring


/-- A matrix which acts as the scalar `c` on the hyperboloid lifts of all points of an open ball
is `c • 1`.  This is the local form of the rigidity of the linear action on the hyperboloid. -/
theorem epd_matrix_eq_smul_one_of_fixes_ball {n : ℕ}
    {M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ} {c : ℝ} {u₀ : Submission.Mostow.E n} {η : ℝ}
    (hn : 1 ≤ n) (hη : 0 < η)
    (h : ∀ u : Submission.Mostow.E n, ‖u - u₀‖ < η →
        Matrix.mulVec M (Submission.Mostow.hlift u) = c • Submission.Mostow.hlift u) :
    M = c • 1 := by
  classical
  have hεpos : (0 : ℝ) < η / 2 := by linarith
  have hcen : ‖u₀ - u₀‖ < η := by rw [sub_self, norm_zero]; exact hη
  have hadd : ∀ x y : Fin n ⊕ Fin 1 → ℝ, M *ᵥ x = c • x → M *ᵥ y = c • y →
      M *ᵥ (x + y) = c • (x + y) := by
    intro x y hx hy; rw [Matrix.mulVec_add, hx, hy, smul_add]
  have hsmul : ∀ (r : ℝ) (x : Fin n ⊕ Fin 1 → ℝ), M *ᵥ x = c • x →
      M *ᵥ (r • x) = c • (r • x) := by
    intro r x hx; rw [Matrix.mulVec_smul, hx, smul_comm]
  have hsub' : ∀ x y : Fin n ⊕ Fin 1 → ℝ, M *ᵥ x = c • x → M *ᵥ y = c • y →
      M *ᵥ (x - y) = c • (x - y) := by
    intro x y hx hy; rw [Matrix.mulVec_sub, hx, hy, smul_sub]
  have hup_mem : ∀ v : E n, ‖v‖ < η → ‖(u₀ + v) - u₀‖ < η := by
    intro v hv
    have h1 : (u₀ + v) - u₀ = v := by abel
    rwa [h1]
  have hum_mem : ∀ v : E n, ‖v‖ < η → ‖(u₀ - v) - u₀‖ < η := by
    intro v hv
    have h1 : (u₀ - v) - u₀ = -v := by abel
    rwa [h1, norm_neg]
  have hnorm_e : ∀ i : Fin n, ‖(η / 2) • EuclideanSpace.single i (1 : ℝ)‖ < η := by
    intro i
    rw [norm_smul, Real.norm_of_nonneg hεpos.le, PiLp.norm_single, norm_one, mul_one]
    linarith
  -- the `(inr 0)`-column
  have hcol_t : M *ᵥ (Pi.single (Sum.inr 0) (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ)
      = c • (Pi.single (Sum.inr 0) (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ) := by
    let i0 : Fin n := ⟨0, by omega⟩
    have hσ : tpart (u₀ + (η / 2) • EuclideanSpace.single i0 (1 : ℝ)) +
        tpart (u₀ - (η / 2) • EuclideanSpace.single i0 (1 : ℝ)) - 2 * tpart u₀ ≠ 0 :=
      ne_of_gt (tpart_second_diff_pos u₀ i0 (ne_of_gt hεpos))
    have hDp : M *ᵥ (hlift (u₀ + (η / 2) • EuclideanSpace.single i0 (1 : ℝ)) - hlift u₀)
        = c • (hlift (u₀ + (η / 2) • EuclideanSpace.single i0 (1 : ℝ)) - hlift u₀) :=
      hsub' _ _ (h _ (hup_mem _ (hnorm_e i0))) (h _ hcen)
    have hDm : M *ᵥ (hlift (u₀ - (η / 2) • EuclideanSpace.single i0 (1 : ℝ)) - hlift u₀)
        = c • (hlift (u₀ - (η / 2) • EuclideanSpace.single i0 (1 : ℝ)) - hlift u₀) :=
      hsub' _ _ (h _ (hum_mem _ (hnorm_e i0))) (h _ hcen)
    have hcomb := hadd _ _ hDp hDm
    rw [hlift_shift_add u₀ i0 (η / 2)] at hcomb
    have h1 := hsmul (tpart (u₀ + (η / 2) • EuclideanSpace.single i0 (1 : ℝ)) +
        tpart (u₀ - (η / 2) • EuclideanSpace.single i0 (1 : ℝ)) - 2 * tpart u₀)⁻¹
      ((tpart (u₀ + (η / 2) • EuclideanSpace.single i0 (1 : ℝ)) +
        tpart (u₀ - (η / 2) • EuclideanSpace.single i0 (1 : ℝ)) - 2 * tpart u₀) •
        (Pi.single (Sum.inr 0) (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ)) hcomb
    rwa [inv_smul_smul₀ hσ] at h1
  -- the `(inl i)`-columns
  have hcol_s : ∀ i : Fin n,
      M *ᵥ (Pi.single (Sum.inl i) (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ)
        = c • (Pi.single (Sum.inl i) (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ) := by
    intro i
    have hD : M *ᵥ (hlift (u₀ + (η / 2) • EuclideanSpace.single i (1 : ℝ)) - hlift u₀)
        = c • (hlift (u₀ + (η / 2) • EuclideanSpace.single i (1 : ℝ)) - hlift u₀) :=
      hsub' _ _ (h _ (hup_mem _ (hnorm_e i))) (h _ hcen)
    rw [hlift_shift_sub u₀ i (η / 2)] at hD
    have hexp : M *ᵥ ((η / 2) • (Pi.single (Sum.inl i) (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ) +
          (tpart (u₀ + (η / 2) • EuclideanSpace.single i (1 : ℝ)) - tpart u₀) •
            (Pi.single (Sum.inr 0) (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ))
        = (η / 2) • (M *ᵥ (Pi.single (Sum.inl i) (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ)) +
          (tpart (u₀ + (η / 2) • EuclideanSpace.single i (1 : ℝ)) - tpart u₀) •
            (c • (Pi.single (Sum.inr 0) (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ)) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hcol_t]
    have hexp' : c • ((η / 2) • (Pi.single (Sum.inl i) (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ) +
          (tpart (u₀ + (η / 2) • EuclideanSpace.single i (1 : ℝ)) - tpart u₀) •
            (Pi.single (Sum.inr 0) (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ))
        = (η / 2) • (c • (Pi.single (Sum.inl i) (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ)) +
          (tpart (u₀ + (η / 2) • EuclideanSpace.single i (1 : ℝ)) - tpart u₀) •
            (c • (Pi.single (Sum.inr 0) (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ)) := by
      rw [smul_add, smul_comm c (η / 2), smul_comm c (tpart (u₀ + (η / 2) •
        EuclideanSpace.single i (1 : ℝ)) - tpart u₀)]
    rw [hexp, hexp'] at hD
    have h2 : (η / 2) • (M *ᵥ (Pi.single (Sum.inl i) (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ))
        = (η / 2) • (c • (Pi.single (Sum.inl i) (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ)) :=
      add_right_cancel hD
    exact smul_right_injective (Fin n ⊕ Fin 1 → ℝ) (ne_of_gt hεpos) h2
  have hcol : ∀ b : Fin n ⊕ Fin 1,
      M *ᵥ (Pi.single b (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ)
        = c • (Pi.single b (1 : ℝ) : Fin n ⊕ Fin 1 → ℝ) := by
    intro b
    rcases b with i | k
    · exact hcol_s i
    · obtain rfl : k = 0 := Subsingleton.elim _ _
      exact hcol_t
  ext a b
  have h2 := congrFun (hcol b) a
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply] at h2
  rw [h2]
  simp [Pi.single_apply, Matrix.one_apply]


/-! ## Fixed sets of isometries of `ℍⁿ` -/

/-- `mat` is injective. -/
theorem epd_mat_injective :
    Function.Injective (mat : O1 n → Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) := by
  intro A B h
  exact Subtype.ext (MatrixSum.ofMatrix.symm.injective h)

/-- `tsign A` is `±1`. -/
lemma tsign_smul_tsign_smul (A : O1 n) (z : Fin n ⊕ Fin 1 → ℝ) :
    tsign A • (tsign A • z) = z := by
  rcases Submission.Mostow.Hyper.tsign_eq_one_or A with h | h <;> rw [h] <;> simp

/-- The set of points fixed by a given element of `PO n 1` is closed. -/
lemma isClosed_fixSet (hA : POActionProp n) (g : PO n 1) : IsClosed {u : E n | g • u = u} := by
  have hcont : Continuous fun u : E n => g • u :=
    (POBasic.ofProp hA).continuous_smul.comp (continuous_const.prodMk continuous_id)
  exact isClosed_eq hcont continuous_id

/-- A nontrivial isometry cannot fix a nonempty open set pointwise. -/
lemma eq_one_of_fixes_isOpen (hn : 1 ≤ n) (hA : POActionProp n) {g : PO n 1} {U : Set (E n)}
    (hU : IsOpen U) (hne : U.Nonempty) (h : ∀ u ∈ U, g • u = u) : g = 1 := by
  obtain ⟨u₀, hu₀⟩ := hne
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hU u₀ hu₀
  have hkey : ∀ u : E n, ‖u - u₀‖ < η →
      Matrix.mulVec (mat (rep g)) (hlift u) = tsign (rep g) • hlift u := by
    intro u hu
    have huU : u ∈ U := hball (Metric.mem_ball.mpr (by simpa [dist_eq_norm] using hu))
    have h1 : hlift u = tsign (rep g) • (Matrix.mulVec (mat (rep g)) (hlift u)) := by
      conv_lhs => rw [← h u huU]
      exact Submission.Mostow.Hyper.hlift_actO (rep g) u
    have h2 := congrArg (fun x => tsign (rep g) • x) h1
    rw [tsign_smul_tsign_smul] at h2
    exact h2.symm
  have hM : mat (rep g) = tsign (rep g) • 1 :=
    epd_matrix_eq_smul_one_of_fixes_ball hn hη hkey
  have hA' : rep g = 1 ∨ rep g = -1 := by
    rcases Submission.Mostow.Hyper.tsign_eq_one_or (rep g) with ht | ht
    · left
      rw [ht, one_smul] at hM
      exact epd_mat_injective (by rw [hM, mat_one])
    · right
      rw [ht] at hM
      simp only [neg_smul, one_smul] at hM
      exact epd_mat_injective (by rw [hM, mat_neg, mat_one])
  have hc : rep g ∈ Subgroup.center (O1 n) := (hA.1 (rep g)).2 hA'
  rw [← QuotientGroup.out_eq' g]
  exact (QuotientGroup.eq_one_iff (rep g)).2 hc

/-- Every nontrivial isometry moves some point of every nonempty open set. -/
lemma exists_smul_ne_self_of_ne_one (hn : 1 ≤ n) (hA : POActionProp n) {g : PO n 1}
    (hg : g ≠ 1) {U : Set (E n)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ u ∈ U, g • u ≠ u := by
  by_contra h
  push_neg at h
  exact hg (eq_one_of_fixes_isOpen hn hA hU hne h)

/-- Given a finite set of nontrivial isometries and a nonempty open set, there is a point of the
open set which is moved by all of them. -/
lemma exists_avoid_smul_finset (hn : 1 ≤ n) (hA : POActionProp n) :
    ∀ t : Finset (PO n 1), (∀ g ∈ t, g ≠ 1) → ∀ U : Set (E n), IsOpen U → U.Nonempty →
      ∃ u ∈ U, ∀ g ∈ t, g • u ≠ u := by
  classical
  intro t
  induction t using Finset.induction_on with
  | empty =>
      intro _ U _ hne
      obtain ⟨u, hu⟩ := hne
      exact ⟨u, hu, by simp⟩
  | insert a s ha ih =>
      intro ht U hU hne
      have ha1 : a ≠ 1 := ht a (Finset.mem_insert_self a s)
      have hs1 : ∀ g ∈ s, g ≠ 1 := fun g hg => ht g (Finset.mem_insert_of_mem hg)
      have hUne' : (U ∩ {u : E n | a • u ≠ u}).Nonempty := by
        obtain ⟨u, hu, hau⟩ := exists_smul_ne_self_of_ne_one hn hA ha1 hU hne
        exact ⟨u, hu, hau⟩
      have hUopen' : IsOpen (U ∩ {u : E n | a • u ≠ u}) :=
        hU.inter (isClosed_fixSet hA a).isOpen_compl
      obtain ⟨u, huU, hua⟩ := ih hs1 (U ∩ {u : E n | a • u ≠ u}) hUopen' hUne'
      refine ⟨u, huU.1, ?_⟩
      intro g hg
      rcases Finset.mem_insert.mp hg with rfl | hgs
      · exact huU.2
      · exact hua g hgs

/-! ## The main statement -/

theorem exists_pos_le_dist {n : ℕ} (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    {Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)}
    (hdisc : IsDiscrete (SetLike.coe Γ)) (hnt : ∃ γ : Γ, γ ≠ 1) :
    ∃ o : Submission.Mostow.E n, ∃ δ : ℝ, 0 < δ ∧
      ∀ γ : Γ, γ ≠ 1 → δ ≤ Submission.Mostow.hdist o
        ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • o) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · -- `ℍ⁰` is a point, so `PO 0 1` is trivial and `hnt` is contradictory
    exfalso
    obtain ⟨γ, hγ⟩ := hnt
    haveI : Subsingleton (Submission.Mostow.E n) := by rw [hn0]; infer_instance
    have h1 : (γ : PO n 1) = 1 :=
      (POBasic.ofProp hA).faithful _ (fun u => Subsingleton.elim _ _)
    exact hγ (Subtype.ext h1)
  · have hdnn : ∀ u v : E n, 0 ≤ hdist u v := hI.1
    have hdsym : ∀ u v : E n, hdist u v = hdist v u := hI.2.1
    have hdzero : ∀ u v : E n, hdist u v = 0 ↔ u = v := hI.2.2.1
    have hdtri : ∀ u v w : E n, hdist u w ≤ hdist u v + hdist v w := hI.2.2.2.1
    have hisom : ∀ (g : PO n 1) (u v : E n), hdist (g • u) (g • v) = hdist u v :=
      hI.2.2.2.2.2.2.1
    -- the finite near-stabiliser of `0`
    have hF : {γ : Γ | hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ 1}.Finite :=
      finite_nearStab (POBasic.ofProp hA) (HypIsoData.ofProp hI) hdisc 1
    -- the nontrivial elements of `F`, as a finset of `PO n 1`
    let t : Finset (PO n 1) :=
      (hF.toFinset.filter (fun γ : Γ => γ ≠ 1)).image (fun γ : Γ => (γ : PO n 1))
    have ht_mem : ∀ γ : Γ, γ ∈ hF.toFinset → γ ≠ 1 → (γ : PO n 1) ∈ t := by
      intro γ hγF hγne
      exact Finset.mem_image.mpr ⟨γ, Finset.mem_filter.mpr ⟨hγF, hγne⟩, rfl⟩
    have ht : ∀ g ∈ t, g ≠ 1 := by
      intro g hg h
      obtain ⟨γ, hγs, hγg⟩ := Finset.mem_image.mp (by simpa only [t] using hg)
      rw [← hγg] at h
      exact (Finset.mem_filter.mp hγs).2 (Subtype.ext (by simpa using h))
    -- a point of the `hdist`-ball of radius `1/4` around `0` avoiding all the fixed sets
    have hUopen : IsOpen {u : E n | hdist (0 : E n) u < (1 : ℝ) / 4} := by
      have hpair : Continuous fun u : E n => ((0 : E n), u) :=
        Continuous.prodMk continuous_const continuous_id
      have h2 : IsOpen {p : E n × E n | hdist p.1 p.2 < (1 : ℝ) / 4} :=
        isOpen_Iio.preimage hI.2.2.2.2.1
      simpa using h2.preimage hpair
    have hUne : ({u : E n | hdist (0 : E n) u < (1 : ℝ) / 4} : Set (E n)).Nonempty :=
      ⟨0, by show hdist (0 : E n) 0 < (1 : ℝ) / 4; rw [(hdzero 0 0).mpr rfl]; norm_num⟩
    obtain ⟨o, ho_ball, ho_avoid⟩ :=
      exists_avoid_smul_finset hn1 hA t ht {u : E n | hdist (0 : E n) u < (1 : ℝ) / 4}
        hUopen hUne
    have ho_lt : hdist (0 : E n) o < (1 : ℝ) / 4 := ho_ball
    -- nontrivial elements of `F` move `o`
    have hFpos : ∀ γ : Γ, γ ∈ hF.toFinset → γ ≠ 1 → 0 < hdist o ((γ : PO n 1) • o) := by
      intro γ hγF hγne
      have hne : (γ : PO n 1) • o ≠ o := ho_avoid _ (ht_mem γ hγF hγne)
      exact lt_of_le_of_ne (hdnn o _) (fun h0 => hne (((hdzero o _).mp h0.symm).symm))
    -- elements outside `F` move `o` by more than `1/2`
    have hbig : ∀ γ : Γ, γ ∉ hF.toFinset → (1 : ℝ) / 2 < hdist o ((γ : PO n 1) • o) := by
      intro γ hγF
      have hgt : 1 < hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) := by
        have hle : ¬ (hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ 1) :=
          fun hc => hγF (hF.mem_toFinset.mpr hc)
        linarith
      have hDh : hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤
          hdist (0 : E n) o + hdist o ((γ : PO n 1) • o) + hdist (0 : E n) o := by
        have hb : hdist o ((γ : PO n 1) • (0 : E n)) ≤
            hdist o ((γ : PO n 1) • o) +
              hdist ((γ : PO n 1) • o) ((γ : PO n 1) • (0 : E n)) := hdtri o _ _
        have hiso2 : hdist ((γ : PO n 1) • o) ((γ : PO n 1) • (0 : E n)) =
            hdist o (0 : E n) := hisom _ o 0
        have hs : hdist o (0 : E n) = hdist (0 : E n) o := hdsym o 0
        linarith [hdtri (0 : E n) o ((γ : PO n 1) • (0 : E n)), hb, hiso2, hs]
      linarith [hgt, hDh, ho_lt, hdnn (0 : E n) o]
    -- the displacements of the nontrivial elements of `F` at `o`
    let vals : Finset ℝ := (hF.toFinset.filter (fun γ : Γ => γ ≠ 1)).image
      (fun γ : Γ => hdist o ((γ : PO n 1) • o))
    have hvals_pos : ∀ r ∈ vals, 0 < r := by
      intro r hr
      obtain ⟨γ, hγs, rfl⟩ := Finset.mem_image.mp (by simpa only [vals] using hr)
      exact hFpos γ (Finset.mem_filter.mp hγs).1 (Finset.mem_filter.mp hγs).2
    by_cases hvals : vals.Nonempty
    · refine ⟨o, min (1 / 2) (vals.min' hvals),
        lt_min (by norm_num) (hvals_pos _ (Finset.min'_mem vals hvals)), ?_⟩
      intro γ hγ
      by_cases hγF : γ ∈ hF.toFinset
      · have hmem : hdist o ((γ : PO n 1) • o) ∈ vals :=
          Finset.mem_image.mpr ⟨γ, Finset.mem_filter.mpr ⟨hγF, hγ⟩, rfl⟩
        exact le_trans (min_le_right _ _) (Finset.min'_le vals _ hmem)
      · exact le_trans (min_le_left _ _) (le_of_lt (hbig γ hγF))
    · refine ⟨o, 1 / 2, by norm_num, ?_⟩
      intro γ hγ
      by_cases hγF : γ ∈ hF.toFinset
      · exact absurd ⟨_, Finset.mem_image.mpr ⟨γ, Finset.mem_filter.mpr ⟨hγF, hγ⟩, rfl⟩⟩ hvals
      · exact le_of_lt (hbig γ hγF)

end

end Work.Mostow
