import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.khintchine_majorArc_real
import Submission.Work.BourgainPlan.IonescuWainger.layer_sunflower_bound_powerset
import Submission.Work.BourgainPlan.IonescuWainger.comp_sum_bound_perTuple

namespace Work.BourgainPlan.IonescuWainger

/-- **The first inequality of Tao's `ortho-apply`(i)** (the description of the `ℓ^{2r}` norm), in
the band-limited `ℓ²(ℤ)` setting: the major-arc system `f_{Σ_A} = Σ_{α ∈ Σ_A} f_α` over
`A ∈ binom(S,≤k)` is controlled by the sums of the shifted systems `f_{α+Σ_{A₀}}` over the cores
`A₀ ∈ binom(S,≤k)` and the arc points `α ∈ Σ_{(A₀)}`.

Route: the hypersystem Khintchine bound `khintchine_majorArc_real` (denominator orthogonality of
the `Σ_A`), the layer-wise sunflower bound `layer_sunflower_bound_powerset` (applied with the
Erdős–Rado threshold `M`), and the per-core rearrangement `comp_sum_bound_perTuple`
(with `ortho`(iii) with core, i.e. Pythagoras for the shifted systems).

The smallness hypotheses are exactly what the two inputs consume; both follow from the
`(r,c)`-goodness condition `ε < c/(2r q_max^{2rk})`, since on a nonce tuple of `2r` sets of
cardinality `≤ k` one has `∏_j Q_{A_j} ≤ q_max^{2rk}`, and on a tuple of pairwise disjoint petals
`Q_{A₀} · ∏_i Q_{A_i} = Q_{A₀ ∪ ⋃_i A_i} ≤ q_max^{r k}` (the union has at most `r k` elements).

Note on conventions: in Tao's own convention `Σ_A = Σ_{⊆A} ∖ ⋃_{B ⊊ A} Σ_{⊆B}` one has
`Σ_{≤k} = ⋃_{A ∈ binom(S,≤k)} Σ_A`, so the left-hand side below is `f_{Σ_{≤k}}`.  The corpus's
`sigmaA` (`ArcDefs.lean`) instead uses *exact denominator* `gcd(a, Q_A) = 1` (which is what makes
the CRT splitting `sigmaAFinset_union_add` hold); the two agree when every element of `S` is prime,
but not for composite elements of `S` (e.g. `S = {4}`: `1/2 ∈ Σ_{⊆{4}}` is in Tao's `Σ_{≤1}` but in
no exact-denominator `Σ_B`).  The identity proved here is therefore stated for the sum over
`A ∈ binom(S,≤k)` of the systems `f_{Σ_A}`. -/
theorem ortho_apply_lower_l2 (k r : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
      (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
      {M : ℕ} (hM : 2 ≤ M)
      (hsun : ∀ T : Finset (Finset ℕ), (∀ A ∈ T, A ⊆ S) → (∀ A ∈ T, A.card ≤ k) → M ≤ T.card →
        ∃ A : Fin r → Finset ℕ, (∀ i, A i ∈ T) ∧ Function.Injective A ∧ IsSunflower A)
      {f : Circle → ℤ → ℂ} (hf : ∀ δ, Memℓp (f δ) 2) {ε : ℝ}
      (hF : ∀ δ, HasFreqSupport (f δ) (hf δ) (arcSet δ ε))
      (hsmallN : ∀ A : Fin r ⊕ Fin r → Finset ℕ, (∀ j, A j ⊆ S ∧ (A j).card ≤ k) → HasNonce A →
        2 * (r : ℝ) * ε < 1 / ((∏ j, QA (A j) : ℕ) : ℝ))
      (hsmallP : ∀ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        ∀ A : (i : Fin r) → ↥((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)),
          (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1)) →
          2 * (r : ℝ) * ε * ((QA A₀ * (∏ i, QA ((A i).1)) : ℕ) : ℝ) < 1),
      ∑' x : ℤ, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), (∑ α ∈ sigmaAFinset A, f α x)‖
          ^ (2 * r)
        ≤ C ^ (k * r) * (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
            ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
              ∑' x : ℤ,
                (∑ α ∈ ((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)).biUnion sigmaAFinset,
                    ‖(∑ γ ∈ sigmaAFinset A₀, f (γ + α) x)‖ ^ 2) ^ r := by
  classical
  obtain ⟨C₁, hC₁pos, hkhi⟩ := khintchine_majorArc_real k r (by omega) hk
  refine ⟨max 1 C₁, lt_max_of_lt_left one_pos, ?_⟩
  intro S h2 hS M hM hsun f hf ε hF hsmallN hsmallP
  -- (0) Denominator orthogonality: the Khintchine/square-function bound for the major-arc hypersystem.
  have hK : (∑' x : ℤ, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        (∑ α ∈ sigmaAFinset A, f α x)‖ ^ (2 * r))
      ≤ C₁ ^ (k * r) * (∑' x : ℤ, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        ‖(∑ α ∈ sigmaAFinset A, f α x)‖ ^ 2) ^ r) :=
    hkhi (S := S) h2 hS (f := f) hf (ε := ε) hF hsmallN
  -- (1) The layer-wise sunflower bound, applied to the major-arc systems.
  have hL : (∑' x : ℤ, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        ‖(∑ α ∈ sigmaAFinset A, f α x)‖ ^ 2) ^ r)
      ≤ (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
          ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
            ∑ A : (i : Fin r) → ↥((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)),
              (if (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1))
               then ∑' x : ℤ, ∏ i, ‖(∑ α ∈ sigmaAFinset (A₀ ∪ (A i).1), f α x)‖ ^ 2
               else 0) :=
    layer_sunflower_bound_powerset (S := S) (k := k) (r := r) (M := M) hr hM hsun
      (f := fun A x => ∑ α ∈ sigmaAFinset A, f α x)
      (fun A => Memℓp.finsetSum (sigmaAFinset A) (fun α _ => hf α))
  -- (2) The per-core rearrangement (`ortho`(iii) with core: Pythagoras for the shifted systems).
  have hP : (∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        ∑ A : (i : Fin r) → ↥((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)),
          (if (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1))
           then ∑' x : ℤ, ∏ i, ‖(∑ α ∈ sigmaAFinset (A₀ ∪ (A i).1), f α x)‖ ^ 2
           else 0))
      ≤ ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
          ∑' x : ℤ,
            (∑ α ∈ ((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)).biUnion sigmaAFinset,
              ‖(∑ γ ∈ sigmaAFinset A₀, f (γ + α) x)‖ ^ 2) ^ r := by
    refine Finset.sum_le_sum (fun A₀ hA₀ => ?_)
    exact comp_sum_bound_perTuple (S := S) (k := k) (r := r) (by omega) h2 hS
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hA₀).1) (f := f) hf (ε := ε) hF
      (hsmallP A₀ hA₀)
  -- the final sum is nonnegative
  have hSumnn : 0 ≤ ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
        ∑' x : ℤ,
          (∑ α ∈ ((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)).biUnion sigmaAFinset,
            ‖(∑ γ ∈ sigmaAFinset A₀, f (γ + α) x)‖ ^ 2) ^ r :=
    Finset.sum_nonneg (fun A₀ _ => tsum_nonneg (fun x =>
      pow_nonneg (Finset.sum_nonneg (fun α _ => sq_nonneg _)) r))
  -- (3) Assembly: `X ≤ A · Σ`, hence `C₁^{kr} · X ≤ C₁^{kr} · A · Σ ≤ C^{kr} · A · Σ`.
  have hX : (∑' x : ℤ, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        ‖(∑ α ∈ sigmaAFinset A, f α x)‖ ^ 2) ^ r)
      ≤ (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
          ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
            ∑' x : ℤ,
              (∑ α ∈ ((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)).biUnion sigmaAFinset,
                ‖(∑ γ ∈ sigmaAFinset A₀, f (γ + α) x)‖ ^ 2) ^ r :=
    hL.trans (mul_le_mul_of_nonneg_left hP (by positivity))
  calc (∑' x : ℤ, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
        (∑ α ∈ sigmaAFinset A, f α x)‖ ^ (2 * r))
      ≤ C₁ ^ (k * r) * (∑' x : ℤ, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k),
          ‖(∑ α ∈ sigmaAFinset A, f α x)‖ ^ 2) ^ r) := hK
    _ ≤ C₁ ^ (k * r) * ((k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
          ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
            ∑' x : ℤ,
              (∑ α ∈ ((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)).biUnion sigmaAFinset,
                ‖(∑ γ ∈ sigmaAFinset A₀, f (γ + α) x)‖ ^ 2) ^ r) :=
        mul_le_mul_of_nonneg_left hX (pow_nonneg hC₁pos.le _)
    _ ≤ (max 1 C₁) ^ (k * r) * ((k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
          ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
            ∑' x : ℤ,
              (∑ α ∈ ((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)).biUnion sigmaAFinset,
                ‖(∑ γ ∈ sigmaAFinset A₀, f (γ + α) x)‖ ^ 2) ^ r) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC₁pos.le (le_max_right 1 C₁) (k * r))
          (mul_nonneg (by positivity) hSumnn)
    _ = (max 1 C₁) ^ (k * r) * (k + 1 : ℝ) ^ (r - 1) * (4 * M : ℝ) ^ r *
          ∑ A₀ ∈ S.powerset.filter (fun A => A.card ≤ k),
            ∑' x : ℤ,
              (∑ α ∈ ((S \ A₀).powerset.filter (fun B => B.card ≤ k - A₀.card)).biUnion sigmaAFinset,
                ‖(∑ γ ∈ sigmaAFinset A₀, f (γ + α) x)‖ ^ 2) ^ r := by ring

end Work.BourgainPlan.IonescuWainger
