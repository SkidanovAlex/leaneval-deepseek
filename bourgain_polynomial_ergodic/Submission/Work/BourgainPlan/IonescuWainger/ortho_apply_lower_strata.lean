import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.StrataCompDefs
import Submission.Work.BourgainPlan.IonescuWainger.ortho_apply_lower_l2
import Submission.Work.BourgainPlan.IonescuWainger.khintchine_majorArc_strata
import Submission.Work.BourgainPlan.IonescuWainger.comp_sum_bound_perTuple_strata

namespace Work.BourgainPlan.IonescuWainger

/-- The first inequality of Tao's `ortho-apply`(i) (the description of the `ℓ^{2r}` norm of the major-arc sum) in **Tao's own strata convention**: for a band-limited major-arc system `f_δ` (Fourier support in `δ + [-ε,ε]`), an Erdős–Rado threshold `M` for the `(k,r)` sunflower statement and the two smallness hypotheses (nonce tuples / disjoint petal tuples), the sum over the strata decomposes as `Σ_{A ∈ binom(S,≤k)} f_{Σ_A}` and obeys `O(r log^{1/2}k)^{-k}‖f_{Σ_{≤k}}‖_{ℓ^{2r}} ≤ (Σ_{A₀} ‖(f_{α+Σ_{A₀}})_{α ∈ Σ_{(A₀)}}‖^{2r}_{ℓ^{2r}(ℓ²)})^{1/2r}`.  This is `ortho_apply_lower_l2` with the exact-denominator sets `sigmaAFinset` replaced everywhere by Tao's strata `sigmaStrataFinset` (so that it matches `opArc_l2_endpoint_strata` / `ortho_apply_upper`, already in the strata convention) and with `Σ_{(A₀)}` written as `strataCompFinset S k A₀`.  Route: repeat the proof of `ortho_apply_lower_l2`, i.e. the strata hypersystem Khintchine bound (`ortho`(ii)) composed with `layer_sunflower_bound_powerset` (Erdős–Rado) and the per-core Pythagoras `comp_sum_bound_perTuple` (`ortho`(iii)).  The strata arithmetic is available: `sigmaLe_separation` applies verbatim to stratum points (they are `arcPt (QA A) a` with `A ⊆ S`, `A.card ≤ k`), and the nonce/petal non-vanishing for strata is `sigmaStrataQ_sum_ne_zero` / `sigmaStrataQ_petal_sum_ne_zero` (with the bridges in `StrataFinsetDefs`/`ZModArcs`); the strata Khintchine/square-function material of the same directory (`khintchine_strata_bound`, `signed_khintchine_strata`, `strata_cluster_square_sum`, `comp_sum_bound`, `comp_sum_bound_perTuple`) is the template. -/
theorem ortho_apply_lower_strata (k r : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
      (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
      {M : ℕ} (hM : 2 ≤ M)
      (hsun : ∀ T : Finset (Finset ℕ), (∀ A ∈ T, A ⊆ S) → (∀ A ∈ T, A.card ≤ k) → M ≤ T.card →
        ∃ A : Fin r → Finset ℕ, (∀ i, A i ∈ T) ∧ Function.Injective A ∧
          Work.BourgainPlan.IonescuWainger.IsSunflower A)
      {f : Work.BourgainPlan.IonescuWainger.Circle → ℤ → ℂ} (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
      (hF : ∀ δ, Work.BourgainPlan.IonescuWainger.HasFreqSupport (f δ) (hf δ)
        (Work.BourgainPlan.IonescuWainger.arcSet δ ε))
      (hsmallN : ∀ A : Fin r ⊕ Fin r → Finset ℕ, (∀ j, A j ⊆ S ∧ (A j).card ≤ k) →
        Work.BourgainPlan.IonescuWainger.HasNonce A →
        2 * (r : ℝ) * ε < 1 / ((∏ j, Work.BourgainPlan.IonescuWainger.QA (A j) : ℕ) : ℝ))
      (hsmallP : ∀ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        ∀ A : (i : Fin r) → ↥((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)),
          (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1)) →
          2 * (r : ℝ) * ε * ((Work.BourgainPlan.IonescuWainger.QA A₀ *
            (∏ i, Work.BourgainPlan.IonescuWainger.QA ((A i).1)) : ℕ) : ℝ) < 1),
      ∑' x : ℤ, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          (∑ α ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A, f α x)‖ ^ (2 * r)
        ≤ C ^ (k * r) * (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
            ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
              ∑' x : ℤ,
                (∑ α ∈ Work.BourgainPlan.IonescuWainger.strataCompFinset S k A₀,
                    ‖(∑ γ ∈ Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A₀,
                      f (γ + α) x)‖ ^ 2) ^ r := by
  classical
  obtain ⟨C₁, hC₁pos, hkhi⟩ := khintchine_majorArc_real_strata k r (by omega) hk
  refine ⟨max 1 C₁, lt_max_of_lt_left one_pos, ?_⟩
  intro S h2 hS M hM hsun f hf ε hF hsmallN hsmallP
  -- (0) the strata Khintchine / square-function bound
  have hK : (∑' x : ℤ, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        (∑ α ∈ sigmaStrataFinset A, f α x)‖ ^ (2 * r))
      ≤ C₁ ^ (k * r) * (∑' x : ℤ, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        ‖(∑ α ∈ sigmaStrataFinset A, f α x)‖ ^ 2) ^ r) :=
    hkhi (S := S) h2 hS (f := f) hf (ε := ε) hF hsmallN
  -- (1) the layer-wise sunflower bound, applied to the major-arc systems
  have hL : (∑' x : ℤ, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        ‖(∑ α ∈ sigmaStrataFinset A, f α x)‖ ^ 2) ^ r)
      ≤ (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
          ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
            ∑ A : (i : Fin r) → ↥((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)),
              (if (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1))
               then ∑' x : ℤ, ∏ i, ‖(∑ α ∈ sigmaStrataFinset (A₀ ∪ (A i).1), f α x)‖ ^ 2
               else 0) :=
    layer_sunflower_bound_powerset (S := S) (k := k) (r := r) (M := M) hr hM hsun
      (f := fun A x => ∑ α ∈ sigmaStrataFinset A, f α x)
      (fun A => Memℓp.finsetSum (sigmaStrataFinset A) (fun α _ => hf α))
  -- (2) the per-core rearrangement (`ortho`(iii) with core: Pythagoras for the shifted systems)
  have hP : (∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        ∑ A : (i : Fin r) → ↥((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)),
          (if (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1))
           then ∑' x : ℤ, ∏ i, ‖(∑ α ∈ sigmaStrataFinset (A₀ ∪ (A i).1), f α x)‖ ^ 2
           else 0))
      ≤ ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
          ∑' x : ℤ,
            (∑ α ∈ strataCompFinset S k A₀,
              ‖(∑ γ ∈ sigmaStrataFinset A₀, f (γ + α) x)‖ ^ 2) ^ r := by
    refine Finset.sum_le_sum (fun A₀ hA₀ => ?_)
    exact comp_sum_bound_perTuple_strata (S := S) (k := k) (r := r) (by omega) h2 hS
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hA₀).1) (f := f) hf (ε := ε) hF
      (hsmallP A₀ hA₀)
  -- the final sum is nonnegative
  have hSumnn : 0 ≤ ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        ∑' x : ℤ,
          (∑ α ∈ strataCompFinset S k A₀,
            ‖(∑ γ ∈ sigmaStrataFinset A₀, f (γ + α) x)‖ ^ 2) ^ r :=
    Finset.sum_nonneg (fun A₀ _ => tsum_nonneg (fun x =>
      pow_nonneg (Finset.sum_nonneg (fun α _ => sq_nonneg _)) r))
  -- (3) assembly
  have hX : (∑' x : ℤ, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        ‖(∑ α ∈ sigmaStrataFinset A, f α x)‖ ^ 2) ^ r)
      ≤ (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
          ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
            ∑' x : ℤ,
              (∑ α ∈ strataCompFinset S k A₀,
                ‖(∑ γ ∈ sigmaStrataFinset A₀, f (γ + α) x)‖ ^ 2) ^ r :=
    hL.trans (mul_le_mul_of_nonneg_left hP (by positivity))
  calc (∑' x : ℤ, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        (∑ α ∈ sigmaStrataFinset A, f α x)‖ ^ (2 * r))
      ≤ C₁ ^ (k * r) * (∑' x : ℤ, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          ‖(∑ α ∈ sigmaStrataFinset A, f α x)‖ ^ 2) ^ r) := hK
    _ ≤ C₁ ^ (k * r) * ((k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
          ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
            ∑' x : ℤ,
              (∑ α ∈ strataCompFinset S k A₀,
                ‖(∑ γ ∈ sigmaStrataFinset A₀, f (γ + α) x)‖ ^ 2) ^ r) :=
        mul_le_mul_of_nonneg_left hX (pow_nonneg hC₁pos.le _)
    _ ≤ (max 1 C₁) ^ (k * r) * ((k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
          ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
            ∑' x : ℤ,
              (∑ α ∈ strataCompFinset S k A₀,
                ‖(∑ γ ∈ sigmaStrataFinset A₀, f (γ + α) x)‖ ^ 2) ^ r) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC₁pos.le (le_max_right 1 C₁) (k * r))
          (mul_nonneg (by positivity) hSumnn)
    _ = (max 1 C₁) ^ (k * r) * (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
          ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
            ∑' x : ℤ,
              (∑ α ∈ strataCompFinset S k A₀,
                ‖(∑ γ ∈ sigmaStrataFinset A₀, f (γ + α) x)‖ ^ 2) ^ r := by ring


end Work.BourgainPlan.IonescuWainger
