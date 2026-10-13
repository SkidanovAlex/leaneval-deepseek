import Mathlib
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG4c.IteratedFDerivPerm
import Submission.Work.WilG4c.BadRayDefs
import Submission.Work.WilG4c.hasFDerivAt_of_dense_tendsto_fderiv
import Submission.Work.WilG4c.ExistsClmTendstoFderivOfCoord
import Submission.Work.WilG4c.CntWordFacts
import Submission.Work.WilG4c.WordCountsLe
import Submission.Work.WilG4c.SumWordCounts
import Submission.Work.WilG4c.IterFDerivFderivDense
import Submission.Work.WilG4c.badRay_interior_eq_empty

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open Filter

namespace Work.WilkG4c

open Work.WilG4c (badRay coordCLM coordCLM_apply_basis norm_le_sum_norm_apply_single
  pre psum psum_eq_pre psum_mono psum_last cntWord_eq_iff wordCounts_cntWord SumWordCounts)

/-! ### Helper lemmas

Two elementary facts about iterated derivatives and the "bad ray" set:

* iterated derivatives only see the germ: functions agreeing on a neighbourhood have the same
  iterated derivatives at the point, and
* the interior of a set is contained in its bad-ray set at every point. -/

private lemma iteratedFDeriv_congr_of_eventuallyEq (N : ℕ) (m : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (f₁ f₂ : (Fin N → ℝ) → F) (x : Fin N → ℝ),
      f₁ =ᶠ[nhds x] f₂ → iteratedFDeriv ℝ m f₁ x = iteratedFDeriv ℝ m f₂ x := by
  induction m with
  | zero =>
    intro F _ _ f₁ f₂ x h
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, h.eq_of_nhds]
  | succ m ih =>
    intro F _ _ f₁ f₂ x h
    ext v
    rw [iteratedFDeriv_succ_apply_right (f := f₁) v, iteratedFDeriv_succ_apply_right (f := f₂) v]
    have h1 := ih (fderiv ℝ f₁) (fderiv ℝ f₂) x h.fderiv
    rw [h1]

private lemma interior_subset_badRay {N : ℕ} (S : Set (Fin N → ℝ)) (u : Fin N → ℝ) :
    interior S ⊆ badRay S u := by
  intro x hx
  obtain ⟨r, hr, hrS⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hxS : x ∈ S := interior_subset hx
  rw [badRay, Set.mem_ofPred_eq]
  rcases eq_or_ne x u with rfl | hxu
  · refine (Set.Ioo_infinite (show (0:ℝ) < 1 by norm_num)).mono ?_
    intro t ht
    exact ⟨⟨ht.1, le_of_lt ht.2⟩, by simpa using hxS⟩
  · have hA : 0 < ‖x - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxu)
    set δ : ℝ := (min r 1 / 2) / (‖x - u‖ + 1) with hδdef
    have hδpos : 0 < δ := by rw [hδdef]; positivity
    have hδr : δ * ‖x - u‖ < r := by
      have h2 : δ * (‖x - u‖ + 1) = min r 1 / 2 := by
        rw [hδdef, div_mul_cancel₀]; positivity
      have h3 : δ * ‖x - u‖ ≤ δ * (‖x - u‖ + 1) := by
        apply mul_le_mul_of_nonneg_left _ hδpos.le
        linarith [norm_nonneg (x - u)]
      rw [h2] at h3
      linarith [min_le_left r 1]
    have hδ1 : δ ≤ 1 := by
      have h2 : δ * (‖x - u‖ + 1) = min r 1 / 2 := by
        rw [hδdef, div_mul_cancel₀]; positivity
      have h3 : δ * 1 ≤ δ * (‖x - u‖ + 1) := by
        have : (1:ℝ) ≤ ‖x - u‖ + 1 := by linarith [norm_nonneg (x - u)]
        exact mul_le_mul_of_nonneg_left this hδpos.le
      rw [h2] at h3
      nlinarith [min_le_right r 1]
    refine (Set.Ioo_infinite (show 1 - δ < 1 by linarith)).mono ?_
    intro t ht
    refine ⟨⟨?_, le_of_lt ht.2⟩, ?_⟩
    · linarith [ht.1]
    · apply hrS
      rw [Metric.mem_ball, dist_eq_norm]
      have hsub : u + t • (x - u) - x = (t - 1) • (x - u) := by module
      rw [hsub, norm_smul, Real.norm_eq_abs]
      have h1 : |t - 1| < δ := by
        rw [abs_of_neg (by linarith [ht.2])]
        linarith [ht.1]
      calc |t - 1| * ‖x - u‖ < δ * ‖x - u‖ := mul_lt_mul_of_pos_right h1 hA
        _ < r := hδr

/-! ### Every word is a permutation of its `cntWord` rearrangement

For a word `v : Fin m → Fin (n+1)`, the word `cntWord n m (wordCounts v)` is the nondecreasing
rearrangement of `v`; here we exhibit an explicit permutation witnessing this.  This is what
turns the `cntWord`-indexed limit hypotheses into limit hypotheses for *all* words. -/

private theorem cntWord_rearrange {n m : ℕ} (v : Fin m → Fin (n + 1)) :
    ∃ σ : Equiv.Perm (Fin m),
      ∀ i : Fin m, v i = cntWord n m (wordCounts v) (σ i) := by
  classical
  have hsum : ∑ i : Fin (n + 1), wordCounts v i = m := SumWordCounts v
  -- the candidate permutation
  have hlt : ∀ i : Fin m,
      pre (wordCounts v) (v i) + (Finset.univ.filter (fun i' : Fin m => i' < i ∧ v i' = v i)).card < m := by
    intro i
    have hle : pre (wordCounts v) (v i) + wordCounts v (v i) ≤ m := by
      calc pre (wordCounts v) (v i) + wordCounts v (v i) = psum (wordCounts v) (v i) :=
            (psum_eq_pre (wordCounts v) (v i)).symm
        _ ≤ psum (wordCounts v) (Fin.last n) := psum_mono (wordCounts v) (v i) (Fin.last n) (Fin.le_last _)
        _ = ∑ j, wordCounts v j := psum_last (wordCounts v)
        _ = m := hsum
    have hsub : (Finset.univ.filter (fun i' : Fin m => i' < i ∧ v i' = v i))
        ⊂ (Finset.univ.filter (fun i' : Fin m => v i' = v i)) := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
      · intro i' hi'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' ⊢
        exact hi'.2
      · intro hcon
        have hmem : i ∈ (Finset.univ.filter (fun i' : Fin m => v i' = v i)) := by simp
        rw [← hcon] at hmem
        simp at hmem
    have hcard : (Finset.univ.filter (fun i' : Fin m => i' < i ∧ v i' = v i)).card
        < wordCounts v (v i) := by
      have := Finset.card_lt_card hsub
      simpa [wordCounts] using this
    omega
  let σ : Fin m → Fin m := fun i =>
    ⟨pre (wordCounts v) (v i)
      + (Finset.univ.filter (fun i' : Fin m => i' < i ∧ v i' = v i)).card, hlt i⟩
  have hσ : ∀ i : Fin m,
      cntWord n m (wordCounts v) (σ i) = v i := by
    intro i
    have h1 : (Finset.univ.filter (fun i' : Fin m => i' < i ∧ v i' = v i)).card
        < wordCounts v (v i) := by
      have hsub : (Finset.univ.filter (fun i' : Fin m => i' < i ∧ v i' = v i))
          ⊂ (Finset.univ.filter (fun i' : Fin m => v i' = v i)) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro i' hi'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' ⊢
          exact hi'.2
        · intro hcon
          have hmem : i ∈ (Finset.univ.filter (fun i' : Fin m => v i' = v i)) := by simp
          rw [← hcon] at hmem
          simp at hmem
      have := Finset.card_lt_card hsub
      simpa [wordCounts] using this
    rw [cntWord_eq_iff (wordCounts v) hsum (σ i) (v i)]
    refine ⟨?_, ?_⟩
    · show pre (wordCounts v) (v i) ≤ (σ i).val
      simp only [σ]
      omega
    · show (σ i).val < pre (wordCounts v) (v i) + wordCounts v (v i)
      simp only [σ]
      omega
  have hinj : Function.Injective σ := by
    intro i i' hii
    have hv : v i = v i' := by
      rw [← hσ i, ← hσ i', hii]
    have hpre : pre (wordCounts v) (v i) = pre (wordCounts v) (v i') := by rw [hv]
    have hcard : (Finset.univ.filter (fun i'' : Fin m => i'' < i ∧ v i'' = v i)).card
        = (Finset.univ.filter (fun i'' : Fin m => i'' < i' ∧ v i'' = v i')).card := by
      have := congrArg Fin.val hii
      simp only [σ] at this
      omega
    rcases lt_trichotomy i i' with h | h | h
    · exfalso
      have hlt2 : (Finset.univ.filter (fun i'' : Fin m => i'' < i ∧ v i'' = v i))
          ⊂ (Finset.univ.filter (fun i'' : Fin m => i'' < i' ∧ v i'' = v i')) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro i'' hi''
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi'' ⊢
          exact ⟨lt_trans hi''.1 h, hi''.2.trans hv⟩
        · intro hcon
          have hmem : i ∈ (Finset.univ.filter (fun i'' : Fin m => i'' < i' ∧ v i'' = v i')) := by
            simp [h, hv]
          rw [← hcon] at hmem
          simp at hmem
      exact absurd hcard (ne_of_lt (Finset.card_lt_card hlt2))
    · exact h
    · exfalso
      have hlt2 : (Finset.univ.filter (fun i'' : Fin m => i'' < i' ∧ v i'' = v i'))
          ⊂ (Finset.univ.filter (fun i'' : Fin m => i'' < i ∧ v i'' = v i)) := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
        · intro i'' hi''
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi'' ⊢
          exact ⟨lt_trans hi''.1 h, hi''.2.trans hv.symm⟩
        · intro hcon
          have hmem : i' ∈ (Finset.univ.filter (fun i'' : Fin m => i'' < i ∧ v i'' = v i)) := by
            simp [h, hv]
          rw [← hcon] at hmem
          simp at hmem
      exact absurd hcard.symm (ne_of_lt (Finset.card_lt_card hlt2))
  refine ⟨Equiv.ofBijective σ ⟨hinj, ?_⟩, fun i => (hσ i).symm⟩
  exact Finite.surjective_of_injective hinj

/-! ### The transfer: `cntWord`-indexed limits give all-word limits

The hypothesis `hlim` of the criterion is indexed by the "counts" vectors `c`, i.e. it only
provides limits along the *sorted* word `cntWord n m c`.  Since `g` is `C^m` off `A` there, the
`m`-th iterated derivative is symmetric (`IteratedFDerivPerm`), and every word is a permutation
of its sorted rearrangement (`CntWordRearrange`), so the limits exist along every word. -/

theorem limits_of_cntWord {n k : ℕ} {g : (Fin (n + 1) → ℝ) → ℝ} {u : Fin (n + 1) → ℝ}
    {ρ : ℝ} {A : Set (Fin (n + 1) → ℝ)}
    (hsm : ∀ y ∈ Metric.ball u ρ, y ∉ A → ContDiffAt ℝ k g y)
    (hlim : ∀ y ∈ Metric.ball u ρ, ∀ m, 1 ≤ m → m ≤ k → ∀ c : Fin (n + 1) → Fin (m + 1),
      ∃ s : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ x, x ∈ Metric.ball u ρ → x ∉ A → x ≠ y → dist x y < δ →
        |iteratedFDeriv ℝ m g x
          (fun i => Pi.single (Work.WilkG4c.cntWord n m (fun j => (c j).val) i) 1) - s| < ε) :
    ∀ y ∈ Metric.ball u ρ, ∀ m, 1 ≤ m → m ≤ k → ∀ v : Fin m → Fin (n + 1),
      ∃ s : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ x, x ∈ Metric.ball u ρ → x ∉ A → x ≠ y → dist x y < δ →
        |iteratedFDeriv ℝ m g x (fun i => Pi.single (v i) 1) - s| < ε := by
  intro y hy m hm1 hmk v
  obtain ⟨σ, hσ⟩ := cntWord_rearrange v
  obtain ⟨s, hs⟩ := hlim y hy m hm1 hmk
    (fun j => ⟨Work.WilkG4c.wordCounts v j, by have h := Work.WilG4c.WordCountsLe v j; omega⟩)
  refine ⟨s, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hδ'⟩ := hs ε hε
  refine ⟨δ, hδ, fun x hx hxA hxy hxd => ?_⟩
  have hw : (fun i : Fin m => (Pi.single (v i) (1 : ℝ) : Fin (n + 1) → ℝ))
      = (fun i : Fin m =>
          (Pi.single (Work.WilkG4c.cntWord n m (Work.WilkG4c.wordCounts v) (σ i)) (1 : ℝ)
            : Fin (n + 1) → ℝ)) := by
    funext i
    rw [hσ i]
  rw [hw, Work.WilG4c.IteratedFDerivPerm
    ((hsm x hx hxA).of_le (by exact_mod_cast hmk)) σ
    (fun j => Work.WilkG4c.cntWord n m (Work.WilkG4c.wordCounts v) j)]
  exact hδ' x hx hxA hxy hxd

/-! ### The dense puncture criterion, by induction on the order

`g` is continuous on the ball, `C^k` off a set `S` whose "bad rays" are thin, and the iterated
derivatives of every order `1, …, k` have limits at every point of the ball along the complement
of `S`.  Then `g` is `C^k` at the centre.  The proof is an induction on `k`: the limits of the
first partials build a candidate derivative `ℓ` (continuous on the ball), which is the genuine
derivative by the mean-value argument along segments meeting `S` only finitely often
(`hasFDerivAt_of_dense_tendsto_fderiv`), and the higher-order limits transport to `ℓ`
(`IterFDerivFderivDense`), so the induction hypothesis applies to `ℓ`. -/

private theorem denseCriterion (N : ℕ) (hN : 1 ≤ N) (k : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (g : (Fin N → ℝ) → F) (u : Fin N → ℝ) (ρ : ℝ) (S : Set (Fin N → ℝ)),
      0 < ρ →
      (∀ y ∈ Metric.ball u ρ, interior (badRay S y) = ∅) →
      ContinuousOn g (Metric.ball u ρ) →
      (∀ x ∈ Metric.ball u ρ, x ∉ S → ContDiffAt ℝ k g x) →
      (∀ y ∈ Metric.ball u ρ, ∀ m, 1 ≤ m → m ≤ k → ∀ v : Fin m → Fin N,
        ∃ s : F, ∀ ε > 0, ∃ δ > 0, ∀ x, x ∈ Metric.ball u ρ → x ∉ S → x ≠ y → dist x y < δ →
          ‖iteratedFDeriv ℝ m g x (fun i => Pi.single (v i) 1) - s‖ < ε) →
      ContDiffAt ℝ k g u := by
  induction k with
  | zero =>
    intro F _ _ g u ρ S hρ hS hcont hsm hlim
    exact (contDiffAt_zero (𝕜 := ℝ) (f := g) (x := u)).mpr
      ⟨Metric.ball u ρ, Metric.ball_mem_nhds u hρ, hcont⟩
  | succ n ih =>
    intro F _ _ g u ρ S hρ hS hcont hsm hlim
    classical
    haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    -- the limit hypotheses in the "no ball membership" shape
    have hlim' : ∀ y ∈ Metric.ball u ρ, ∀ m, 1 ≤ m → m ≤ n + 1 → ∀ v : Fin m → Fin N,
        ∃ s : F, ∀ ε > 0, ∃ δ > 0, ∀ x, x ≠ y → x ∉ S → dist x y < δ →
          ‖iteratedFDeriv ℝ m g x (fun i => Pi.single (v i) 1) - s‖ < ε := by
      intro y hy m hm1 hmk v
      obtain ⟨s, hs⟩ := hlim y hy m hm1 hmk v
      refine ⟨s, fun ε hε => ?_⟩
      obtain ⟨δ, hδ, hδ'⟩ := hs ε hε
      refine ⟨min δ (ρ - dist y u), lt_min hδ (sub_pos.mpr (Metric.mem_ball.mp hy)),
        fun x hxy hxS hxd => ?_⟩
      refine hδ' x ?_ hxS hxy (lt_of_lt_of_le hxd (min_le_left _ _))
      rw [Metric.mem_ball]
      calc dist x u ≤ dist x y + dist y u := dist_triangle _ _ _
        _ < min δ (ρ - dist y u) + dist y u := by linarith [lt_of_lt_of_le hxd (min_le_left _ _)]
        _ ≤ ρ := by linarith [min_le_right δ (ρ - dist y u)]
    -- (1) the first-order limits and the candidate derivative
    have hlim1 : ∀ y ∈ Metric.ball u ρ, ∀ j : Fin N, ∃ s : F, ∀ ε > 0, ∃ δ > 0,
        ∀ x, x ≠ y → x ∉ S → dist x y < δ →
          ‖fderiv ℝ g x (Pi.single j 1) - s‖ < ε := by
      intro y hy j
      obtain ⟨s, hs⟩ := hlim' y hy 1 le_rfl (Nat.le_add_left 1 n) (fun _ : Fin 1 => j)
      refine ⟨s, fun ε hε => ?_⟩
      obtain ⟨δ, hδ, hδ'⟩ := hs ε hε
      refine ⟨δ, hδ, fun x hxy hxS hxd => ?_⟩
      have h1 : iteratedFDeriv ℝ 1 g x (fun _ : Fin 1 => (Pi.single j (1:ℝ) : Fin N → ℝ))
          = fderiv ℝ g x (Pi.single j 1) := iteratedFDeriv_one_apply _
      rw [← h1]
      exact hδ' x hxy hxS hxd
    choose s1 hs1 using hlim1
    have hex : ∀ y : Fin N → ℝ, ∃ f : Fin N → F,
        ∀ hy : y ∈ Metric.ball u ρ, ∀ j, f j = s1 y hy j := by
      intro y
      by_cases hy : y ∈ Metric.ball u ρ
      · exact ⟨s1 y hy, fun hy' j => rfl⟩
      · exact ⟨fun _ => 0, fun hy' _ => absurd hy' hy⟩
    let Lc : (Fin N → ℝ) → Fin N → F := fun y => Classical.choose (hex y)
    let ℓ : (Fin N → ℝ) → (Fin N → ℝ) →L[ℝ] F := fun y => coordCLM (Lc y)
    have hLc : ∀ y hy j, Lc y j = s1 y hy j := fun y hy j => Classical.choose_spec (hex y) hy j
    have hℓcoord : ∀ y ∈ Metric.ball u ρ, ∀ j : Fin N, ∀ ε > 0, ∃ δ > 0,
        ∀ x, x ≠ y → x ∉ S → dist x y < δ →
          ‖fderiv ℝ g x (Pi.single j 1) - ℓ y (Pi.single j 1)‖ < ε := by
      intro y hy j ε hε
      have h := hs1 y hy j ε hε
      have h2 : ℓ y (Pi.single j 1) = s1 y hy j := by
        simp only [ℓ, coordCLM_apply_basis, hLc y hy j]
      simpa [h2] using h
    have hℓtend : ∀ y ∈ Metric.ball u ρ, ∀ ε > 0, ∃ δ > 0,
        ∀ x, x ≠ y → x ∉ S → dist x y < δ →
          ‖fderiv ℝ g x - ℓ y‖ < ε := by
      intro y hy ε hε
      have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
      have hstep : ∀ j : Fin N, ∃ δ : ℝ, 0 < δ ∧ ∀ x, x ≠ y → x ∉ S →
          dist x y < δ → ‖fderiv ℝ g x (Pi.single j 1) - ℓ y (Pi.single j 1)‖ < ε / N :=
        fun j => hℓcoord y hy j (ε / N) (by positivity)
      choose δ hδpos hδ using hstep
      refine ⟨Finset.univ.inf' Finset.univ_nonempty δ, ?_, ?_⟩
      · exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun j _ => hδpos j)
      · intro x hxy hxS hxd
        have hb : ∀ j : Fin N,
            ‖fderiv ℝ g x (Pi.single j 1) - ℓ y (Pi.single j 1)‖ < ε / N := fun j =>
          hδ j x hxy hxS (lt_of_lt_of_le hxd (Finset.inf'_le δ (Finset.mem_univ j)))
        calc ‖fderiv ℝ g x - ℓ y‖
            ≤ ∑ j : Fin N, ‖(fderiv ℝ g x - ℓ y) (Pi.single j 1)‖ :=
              norm_le_sum_norm_apply_single _
          _ = ∑ j : Fin N, ‖fderiv ℝ g x (Pi.single j 1) - ℓ y (Pi.single j 1)‖ := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [sub_apply]
          _ < ∑ _j : Fin N, ε / N :=
              Finset.sum_lt_sum (fun j _ => (hb j).le)
                ⟨⟨0, hN⟩, Finset.mem_univ _, hb ⟨0, hN⟩⟩
          _ = ε := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm,
                div_mul_cancel₀ _ hNpos.ne']
    -- (2) differentiability at every point of the ball
    have hderiv : ∀ y ∈ Metric.ball u ρ, HasFDerivAt g (ℓ y) y := by
      intro y hy
      have hyρ : 0 < ρ - dist y u := sub_pos.mpr (Metric.mem_ball.mp hy)
      have hsub : Metric.ball y (ρ - dist y u) ⊆ Metric.ball u ρ := by
        intro z hz
        rw [Metric.mem_ball] at hz ⊢
        calc dist z u ≤ dist z y + dist y u := dist_triangle _ _ _
          _ < (ρ - dist y u) + dist y u := by linarith
          _ = ρ := by ring
      exact Work.WilG4c.hasFDerivAt_of_dense_tendsto_fderiv hN hyρ (S := S) (g := g)
        (u := y) (ρ := ρ - dist y u) (hS y hy) (hcont.mono hsub)
        (fun x hx hxy hxS => (hsm x (hsub hx) hxS).differentiableAt (by simp))
        (hℓtend y hy)
    -- (3) the candidate derivative is continuous on the ball
    have hSempty : interior S = ∅ := by
      have h1 : interior S ⊆ interior (badRay S u) :=
        interior_maximal (interior_subset_badRay S u) isOpen_interior
      rw [hS u (Metric.mem_ball_self hρ)] at h1
      exact Set.eq_empty_of_subset_empty h1
    have hdense : Dense Sᶜ := interior_eq_empty_iff_dense_compl.mp hSempty
    have hℓcont : ContinuousOn ℓ (Metric.ball u ρ) := by
      intro y hy
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hℓtend y hy (ε / 2) (by linarith)
      refine ⟨δ₁ / 2, by linarith, ?_⟩
      intro z hz hzd
      have hzy : dist z y < δ₁ := by linarith
      obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := hℓtend z hz (ε / 2) (by linarith)
      have hminpos : 0 < min δ₂ (δ₁ - dist z y) := lt_min hδ₂pos (by linarith)
      obtain ⟨x, hxS, hxball⟩ := hdense.exists_mem_open Metric.isOpen_ball
        ⟨z, Metric.mem_ball_self hminpos⟩
      rw [Metric.mem_ball] at hxball
      have hxdz : dist x z < δ₂ := lt_of_lt_of_le hxball (min_le_left _ _)
      have hxdy : dist x y < δ₁ := by
        have h1 : dist x z < δ₁ - dist z y := lt_of_lt_of_le hxball (min_le_right _ _)
        calc dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
          _ < δ₁ := by linarith
      have h1 : ‖fderiv ℝ g x - ℓ z‖ < ε / 2 := by
        rcases eq_or_ne x z with hxz | hxz
        · rw [hxz, (hderiv z hz).fderiv, sub_self, norm_zero]; linarith
        · exact hδ₂ x hxz hxS hxdz
      have h2 : ‖fderiv ℝ g x - ℓ y‖ < ε / 2 := by
        rcases eq_or_ne x y with hxy | hxy
        · rw [hxy, (hderiv y hy).fderiv, sub_self, norm_zero]; linarith
        · exact hδ₁ x hxy hxS hxdy
      calc dist (ℓ z) (ℓ y) = ‖ℓ z - ℓ y‖ := dist_eq_norm _ _
        _ ≤ ‖ℓ z - fderiv ℝ g x‖ + ‖fderiv ℝ g x - ℓ y‖ := by
            rw [show ℓ z - ℓ y = (ℓ z - fderiv ℝ g x) + (fderiv ℝ g x - ℓ y) from by abel]
            exact norm_add_le _ _
        _ = ‖fderiv ℝ g x - ℓ z‖ + ‖fderiv ℝ g x - ℓ y‖ := by
            rw [norm_sub_rev (fderiv ℝ g x) (ℓ z)]
        _ < ε := by linarith
    -- (4) the candidate derivative is `C^n` off `S`
    have hℓsm : ∀ x ∈ Metric.ball u ρ, x ∉ S → ContDiffAt ℝ n ℓ x := by
      intro x hx hxS
      have hn1 : ((n + 1 : ℕ) : WithTop ℕ∞) = ((n : ℕ) : WithTop ℕ∞) + 1 := by
        push_cast; ring
      have hfd : ContDiffAt ℝ (n : ℕ) (fderiv ℝ g) x :=
        ContDiffAt.fderiv_right_succ (n := ((n : ℕ) : WithTop ℕ∞))
          (by rw [← hn1]; exact hsm x hx hxS)
      refine hfd.congr_of_eventuallyEq ?_
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
      exact (hderiv z hz).fderiv.symm
    -- (5) the limit conditions for the candidate derivative
    have hℓlim : ∀ y ∈ Metric.ball u ρ, ∀ m, 1 ≤ m → m ≤ n → ∀ v : Fin m → Fin N,
        ∃ s : (Fin N → ℝ) →L[ℝ] F, ∀ ε > 0, ∃ δ > 0, ∀ x, x ∈ Metric.ball u ρ → x ∉ S →
          x ≠ y → dist x y < δ →
          ‖iteratedFDeriv ℝ m ℓ x (fun i => Pi.single (v i) 1) - s‖ < ε := by
      intro y hy m hm1 hmn v
      obtain ⟨s, hs⟩ := Work.WilG4c.IterFDerivFderivDense hN (g := g) (u := y) (S := S) (m := m)
        (fun w => hlim' y hy (m + 1) (by omega) (by omega) w) v
      refine ⟨s, fun ε hε => ?_⟩
      obtain ⟨δ, hδ, hδ'⟩ := hs ε hε
      refine ⟨δ, hδ, fun x hx hxS hxy hxd => ?_⟩
      have hcongr : iteratedFDeriv ℝ m ℓ x
          = iteratedFDeriv ℝ m (fun z => fderiv ℝ g z) x := by
        refine iteratedFDeriv_congr_of_eventuallyEq N m ℓ _ x ?_
        filter_upwards [Metric.isOpen_ball.mem_nhds hx] with z hz
        exact (hderiv z hz).fderiv.symm
      rw [hcongr]
      exact hδ' x hxy hxS hxd
    -- (6) the induction hypothesis gives `C^n` of the candidate derivative at `u`
    have hℓC : ContDiffAt ℝ n ℓ u := ih ℓ u ρ S hρ hS hℓcont hℓsm hℓlim
    -- (7) reassemble
    have hk : ((n + 1 : ℕ) : WithTop ℕ∞) = ((n : ℕ) : WithTop ℕ∞) + 1 := by push_cast; ring
    rw [hk]
    exact (contDiffAt_succ_iff_hasFDerivAt (𝕜 := ℝ) (f := g) (x := u) (n := n)).mpr
      ⟨ℓ, ⟨Metric.ball u ρ, Metric.ball_mem_nhds u hρ, fun x hx => hderiv x hx⟩, hℓC⟩

theorem DensePunctureCriterion (S : WilkiesDesign.SOMin) (hcd : S.SharpCD)
    {n k : ℕ} {g : (Fin (n + 1) → ℝ) → ℝ} {u : Fin (n + 1) → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    {F D : ℕ} {A : Set (Fin (n + 1) → ℝ)} (hA : A ∈ S.Ω F D (n + 1))
    (hAthin : interior A = ∅) (hAclosed : IsClosed A)
    (hcont : ContinuousOn g (Metric.ball u ρ))
    (hsm : ∀ y ∈ Metric.ball u ρ, y ∉ A → ContDiffAt ℝ k g y)
    (hlim : ∀ y ∈ Metric.ball u ρ, ∀ m, 1 ≤ m → m ≤ k → ∀ c : Fin (n + 1) → Fin (m + 1),
      ∃ s : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ x, x ∈ Metric.ball u ρ → x ∉ A → x ≠ y → dist x y < δ →
        |iteratedFDeriv ℝ m g x
          (fun i => Pi.single (Work.WilkG4c.cntWord n m (fun j => (c j).val) i) 1) - s| < ε) :
    ContDiffAt ℝ k g u := by
  have hlimAll := limits_of_cntWord hsm hlim
  have hSthin : ∀ y ∈ Metric.ball u ρ, interior (badRay A y) = ∅ := by
    intro y hy
    exact Work.WilG4c.badRay_interior_eq_empty S hcd (n + 1) F D A y hA hAthin
  exact denseCriterion (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) k g u ρ A hρ hSthin hcont hsm
    hlimAll

end Work.WilkG4c

/-! The same statement under the namespace used by the module path (`Work.WilG4c`), so that both
`Work.WilkG4c.DensePunctureCriterion` and `Work.WilG4c.DensePunctureCriterion` resolve. -/

namespace Work.WilG4c

theorem DensePunctureCriterion (S : WilkiesDesign.SOMin) (hcd : S.SharpCD)
    {n k : ℕ} {g : (Fin (n + 1) → ℝ) → ℝ} {u : Fin (n + 1) → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    {F D : ℕ} {A : Set (Fin (n + 1) → ℝ)} (hA : A ∈ S.Ω F D (n + 1))
    (hAthin : interior A = ∅) (hAclosed : IsClosed A)
    (hcont : ContinuousOn g (Metric.ball u ρ))
    (hsm : ∀ y ∈ Metric.ball u ρ, y ∉ A → ContDiffAt ℝ k g y)
    (hlim : ∀ y ∈ Metric.ball u ρ, ∀ m, 1 ≤ m → m ≤ k → ∀ c : Fin (n + 1) → Fin (m + 1),
      ∃ s : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ x, x ∈ Metric.ball u ρ → x ∉ A → x ≠ y → dist x y < δ →
        |iteratedFDeriv ℝ m g x
          (fun i => Pi.single (Work.WilkG4c.cntWord n m (fun j => (c j).val) i) 1) - s| < ε) :
    ContDiffAt ℝ k g u :=
  Work.WilkG4c.DensePunctureCriterion S hcd hρ hA hAthin hAclosed hcont hsm hlim

end Work.WilG4c
