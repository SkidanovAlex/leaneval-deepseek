import Mathlib
import Submission.Work.Projection.dimH_image_le_of_contDiffOn

set_option maxHeartbeats 1600000

open scoped ContDiff

namespace Work.Drive.Whitney

open MeasureTheory

/-- Appending a one-tuple to `Fin.append b v`, reindexed by the canonical identification
`Fin ((2+j)+1) ≃ Fin (2+(j+1))`, is the same as appending the snoc: `Fin.append b (Fin.snoc v c)`. -/
theorem fin_append_append_one {α : Type*} {j : ℕ} (b : Fin 2 → α) (v : Fin j → α) (c : α) :
    Fin.append (Fin.append b v) (fun _ : Fin 1 => c) ∘ Fin.cast (Nat.add_assoc 2 j 1).symm
      = Fin.append b (Fin.snoc v c) := by
  rw [Fin.append_assoc, Fin.append_right_eq_snoc]
  ext i
  simp

/-- **Filling a family of independent vectors up to a family of independent vectors, uniformly over
a compact parameter set.**  Given a compact `K ⊆ ℝ²`, a `C^∞` family `T p` of two independent
vectors, a `C^∞` family `U₀ p` of `k` vectors and a `C^∞` scalar `β` such that the concatenation is
independent wherever `β` vanishes, there is a single tuple `w` of `k` vectors such that
`U₀ p i + β p • w i` is independent together with `T p` for all `p ∈ K`.

The vectors `w i` are chosen one at a time.  At stage `j < k` the vectors chosen so far span, for
each parameter `p` with `β p ≠ 0`, the subspace `famfun p = span (range (Fin.append (T p) ·))` of
dimension `2 + j`, and the `j`-th vector has to avoid the affine subspace
`(β p)⁻¹ • (-U₀ p j) + famfun p`.  The union of these subspaces over the *whole* parameter set is
the image of the `C^∞` map

`Φ (p, y) = (β p)⁻¹ • (-U₀ p j) + ∑ t, y t • famfun p t`

on the open set `{β ≠ 0} × univ`, whose source has dimension `2 + (2 + j) = j + 4 ≤ k + 3 < n`, so
`dimH (range Φ) ≤ j + 4 < finrank ℝ F`; Mathlib's Sard-lite `dense_compl_of_dimH_lt_finrank` (via
`Work.Projection.dimH_image_le_of_contDiffOn`) then produces the required vector.  Note that the
compactness of `K` is *not* used: the dimension bound only depends on the dimension of the source.

At the end, the points of `K` at which `β` vanishes are handled by the hypothesis `hindU`. -/
theorem exists_injective_fill {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    {k : ℕ} (hk : k + 4 ≤ Module.finrank ℝ F)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (T : ℝ × ℝ → Fin 2 → F) (hT : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) T)
    (hindT : ∀ p ∈ K, LinearIndependent ℝ (T p))
    (U₀ : ℝ × ℝ → Fin k → F) (hU₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U₀)
    (β : ℝ × ℝ → ℝ) (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hindU : ∀ p ∈ K, β p = 0 → LinearIndependent ℝ (Fin.append (T p) (U₀ p))) :
    ∃ w : Fin k → F, ∀ p ∈ K,
      LinearIndependent ℝ (Fin.append (T p) (fun i => U₀ p i + β p • w i)) := by
  classical
  -- `hK` (compactness of `K`) is not needed: the dimension bound below only uses the dimension of
  -- the source of the parametrisation, not the size of `K`.
  have _ : IsCompact K := hK
  have hβc : Continuous β := hβ.continuous
  -- The induction: for each `j ≤ k` we choose the first `j` vectors of `w` so that the
  -- corresponding `2 + j` vectors are independent at every point of `K` at which `β ≠ 0`.
  have key : ∀ (j : ℕ) (hjk0 : j ≤ k), ∃ w : Fin j → F,
      ∀ p ∈ K \ {q : ℝ × ℝ | β q = 0},
        LinearIndependent ℝ (Fin.append (T p)
          (fun i : Fin j => U₀ p (Fin.castLE hjk0 i) + β p • w i)) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨Fin.elim0, ?_⟩
      intro p hp
      have hz0 : (fun i : Fin 0 => U₀ p (Fin.castLE (Nat.zero_le k) i) +
            β p • (Fin.elim0 : Fin 0 → F) i) = Fin.elim0 := by
        funext i
        exact i.elim0
      rw [hz0, Fin.append_elim0]
      exact (linearIndependent_equiv (finCongr (Nat.add_zero 2)) (f := T p)).mpr (hindT p hp.1)
    | succ j ih =>
      intro hjk
      obtain ⟨w, hw⟩ := ih (Nat.le_of_succ_le hjk)
      have hj : j < k := Nat.lt_of_succ_le hjk
      have hj' : j ≤ k := Nat.le_of_succ_le hjk
      have hlast : Fin.castLE hjk (Fin.last j) = (⟨j, hj⟩ : Fin k) := Fin.ext (by simp)
      -- the family chosen so far, as a function of the parameter
      set famfun : (ℝ × ℝ) → (Fin (2 + j) → F) :=
        fun q => Fin.append (T q) (fun i : Fin j => U₀ q (Fin.castLE hj' i) + β q • w i)
        with hfamfun
      -- The parametrisation of the "bad" set of the `j`-th vector: those `z` for which
      -- `U₀ p · + β p • z` falls into the span of the previously chosen vectors.
      set Φ : (ℝ × ℝ) × (Fin (2 + j) → ℝ) → F :=
        fun q => (β q.1)⁻¹ • (-(U₀ q.1 ⟨j, hj⟩)) +
          ∑ t : Fin (2 + j), q.2 t • famfun q.1 t with hΦ
      set U : Set ((ℝ × ℝ) × (Fin (2 + j) → ℝ)) := {q | β q.1 ≠ 0} with hU
      set tt : Set ((ℝ × ℝ) × (Fin (2 + j) → ℝ)) :=
        {q | q.1 ∈ K \ {r : ℝ × ℝ | β r = 0}} with htt
      have hUopen : IsOpen U := by
        rw [hU]
        exact isOpen_ne.preimage (hβc.comp continuous_fst)
      have hΦsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ U := by
        rw [hΦ]
        refine ContDiffOn.add ?_ ?_
        · refine ContDiffOn.smul ?_ ?_
          · exact ContDiffOn.inv ((hβ.comp contDiff_fst).contDiffOn)
              (fun q hq => by rw [hU] at hq; exact hq)
          · exact ((contDiffOn_const (c := ContinuousLinearMap.proj (R := ℝ)
              (φ := fun _ : Fin k => F) ⟨j, hj⟩)).clm_apply
              ((hU₀.comp contDiff_fst).contDiffOn)).neg
        · have hfam_t : ∀ t : Fin (2 + j), ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
              (fun q : (ℝ × ℝ) × (Fin (2 + j) → ℝ) => famfun q.1 t) U := by
            intro t
            rw [hfamfun]
            revert t
            refine Fin.addCases ?_ ?_
            · intro a
              simp only [Fin.append_left]
              exact (contDiffOn_const (c := ContinuousLinearMap.proj (R := ℝ)
                (φ := fun _ : Fin 2 => F) a)).clm_apply ((hT.comp contDiff_fst).contDiffOn)
            · intro i
              simp only [Fin.append_right]
              refine ContDiffOn.add ?_ ?_
              · exact (contDiffOn_const (c := ContinuousLinearMap.proj (R := ℝ)
                  (φ := fun _ : Fin k => F) (Fin.castLE hj' i))).clm_apply
                  ((hU₀.comp contDiff_fst).contDiffOn)
              · exact ((hβ.comp contDiff_fst).contDiffOn).smul contDiffOn_const
          refine ContDiffOn.sum (s := Finset.univ) (fun t _ => ?_)
          refine ContDiffOn.smul (f := fun q : (ℝ × ℝ) × (Fin (2 + j) → ℝ) => q.2 t)
            (g := fun q : (ℝ × ℝ) × (Fin (2 + j) → ℝ) => famfun q.1 t) ?_ ?_
          · exact (contDiffOn_const (c := ContinuousLinearMap.proj (R := ℝ)
              (φ := fun _ : Fin (2 + j) => ℝ) t)).clm_apply
              ((contDiff_snd (𝕜 := ℝ) (E := ℝ × ℝ) (F := Fin (2 + j) → ℝ)).contDiffOn)
          · exact hfam_t t
      have hΦ1 : ContDiffOn ℝ 1 Φ U := hΦsm.of_le (by simp)
      have hsub : tt ⊆ U := by
        intro q hq
        rw [htt] at hq
        rw [hU]
        exact hq.2
      have hfr : Module.finrank ℝ ((ℝ × ℝ) × (Fin (2 + j) → ℝ)) < Module.finrank ℝ F := by
        rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self ℝ, Module.finrank_pi,
          Fintype.card_fin]
        omega
      have hdim : dimH (Φ '' tt) < Module.finrank ℝ F := by
        refine lt_of_le_of_lt (Work.Projection.dimH_image_le_of_contDiffOn hUopen hΦ1 hsub) ?_
        exact_mod_cast hfr
      obtain ⟨z, hz⟩ := (dense_compl_of_dimH_lt_finrank hdim).nonempty
      -- `z` is not in the bad set: the new vector is never in the span of the previous ones.
      have hnotin : ∀ p ∈ K \ {q : ℝ × ℝ | β q = 0},
          U₀ p ⟨j, hj⟩ + β p • z ∉ Submodule.span ℝ (Set.range (famfun p)) := by
        intro p hp hbad
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hbad
        refine hz ⟨(p, fun t => (β p)⁻¹ * c t), ?_, ?_⟩
        · rw [htt]; exact hp
        · rw [hΦ]
          simp only []
          have hsum : (∑ t : Fin (2 + j), ((β p)⁻¹ * c t) • famfun p t)
              = (β p)⁻¹ • (U₀ p ⟨j, hj⟩ + β p • z) := by
            rw [← hc, Finset.smul_sum]
            refine Finset.sum_congr rfl (fun t _ => ?_)
            rw [← smul_eq_mul]
            exact smul_assoc _ _ _
          rw [hsum, ← smul_add, neg_add_cancel_left, inv_smul_smul₀ hp.2]
      refine ⟨Fin.snoc w z, ?_⟩
      intro p hp
      have hLIj : LinearIndependent ℝ (famfun p) := by
        rw [hfamfun]; exact hw p hp
      have hsnoc : LinearIndependent ℝ
          (Fin.snoc (famfun p) (U₀ p ⟨j, hj⟩ + β p • z)) :=
        hLIj.finSnoc (hnotin p hp)
      have hA : LinearIndependent ℝ
          (Fin.append (famfun p) (fun _ : Fin 1 => U₀ p ⟨j, hj⟩ + β p • z)) := by
        rw [Fin.append_right_eq_snoc]
        exact hsnoc
      have hv' : (fun i : Fin (j + 1) => U₀ p (Fin.castLE hjk i) +
              β p • (Fin.snoc (α := fun _ => F) w z) i)
          = Fin.snoc (α := fun _ => F)
              (fun i : Fin j => U₀ p (Fin.castLE hj' i) + β p • w i)
              (U₀ p ⟨j, hj⟩ + β p • z) := by
        funext i
        refine Fin.lastCases ?_ ?_ i
        · simp only [Fin.snoc_last, hlast]
        · intro i
          simp only [Fin.snoc_castSucc, Fin.castLE_castSucc]
      rw [hv']
      exact (linearIndependent_equiv' ((finCongr (Nat.add_assoc 2 j 1)).symm)
        (by rw [hfamfun]; exact fin_append_append_one (T p) _ _)).mpr hA
  -- Assemble: on `K` either `β` vanishes (hypothesis) or the induction applies.
  obtain ⟨w, hw⟩ := key k le_rfl
  refine ⟨w, ?_⟩
  intro p hp
  by_cases hβp : β p = 0
  · have h1 : (fun i : Fin k => U₀ p i + β p • w i) = U₀ p := by
      funext i; rw [hβp, zero_smul, add_zero]
    rw [h1]
    exact hindU p hp hβp
  · have hp' : p ∈ K \ {q : ℝ × ℝ | β q = 0} := ⟨hp, by simpa using hβp⟩
    have h2 := hw p hp'
    have h3 : (fun i : Fin k => U₀ p (Fin.castLE (le_refl k) i) + β p • w i)
        = fun i : Fin k => U₀ p i + β p • w i := by
      funext i; rw [Fin.castLE_rfl]; rfl
    rwa [h3] at h2

end Work.Drive.Whitney
