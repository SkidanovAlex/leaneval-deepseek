import Mathlib
import Submission.Theorem36iSep
import Submission.SieveWeight

open scoped BigOperators Topology
open Filter Finset

set_option maxHeartbeats 1000000

/-!
# The `S₁` bound (Polymath8a (13)) with *separated* pairwise support conditions

`weightSum_tpWeight_le_pairwise` (in `Submission/SieveWeight.lean`) controls
`Σ_{n ≡ b (W)} ν(n)` for the tensor-product sieve weight under the pairwise
condition `2·Σᵢ max (M j i) (M j' i) < 1`.  In the §5.3 application the two
component families `f_{j,·}` and `f_{j',·}` are localised in *different*
coordinates, so that condition need not hold; the correct one is
Polymath8a (27), `Σᵢ (S(f_{j,i}) + S(f_{j',i})) < 1`, i.e. the *sum* of the two
support budgets — supplied here (together with the common truncation bound `Mc`
for the divisor sums) as `hMpair` and `hMc`.
-/

namespace Commons.NumberTheory.MaynardSieve


/-- **Polymath8a Theorem 3.6(i), separated support bounds, real form**: the
`ℝ`-valued version consumed by the sieve (`mainTargetR`). -/
theorem theorem36_i_real_sep {k : ℕ} (hk : 1 ≤ k) (H : Fin k → ℕ)
    (hHinj : Function.Injective H)
    (F G : Fin k → ℝ → ℝ) (hcsF : ∀ i, HasCompactSupport (F i))
    (hsmF : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (F i)) (hcsG : ∀ i, HasCompactSupport (G i))
    (hsmG : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (G i))
    (MF MG : Fin k → ℝ) (hMFnn : ∀ i, 0 ≤ MF i) (hMGnn : ∀ i, 0 ≤ MG i)
    (hsuppF : ∀ i t, MF i < |t| → F i t = 0)
    (hsuppG : ∀ i t, MG i < |t| → G i t = 0)
    (hσ : (∑ i, MF i) + (∑ i, MG i) < 1)
    {Mc : ℝ} (hMc : ∀ i t, Mc < |t| → F i t = 0 ∧ G i t = 0)
    (W : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x)
    (hlq : Tendsto (fun x : ℕ => Real.log (W x : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0))
    (D : ℕ → ℕ) (hD : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ Mc ≤ (D x : ℝ))
    (b : ℕ → ℕ) (hbW : ∀ x i, (b x + H i).Coprime (W x)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ x : ℕ, x₀ ≤ x →
      |windowDivisorProduct F G H (W x) (b x) (D x) x - mainTargetR F G W x| ≤
        ε x * mainScale k W x := by
  obtain ⟨x₀, ε, hε, hb⟩ := theorem36_i_sep_uncond hk H hHinj F G hcsF hsmF hcsG hsmG
    MF MG hMFnn hMGnn hsuppF hsuppG hσ hMc W hW w hw hsmall hlq D hD b hbW
  refine ⟨x₀, ε, hε, fun x hx => ?_⟩
  have h := hb x hx
  have key : (((windowDivisorProduct F G H (W x) (b x) (D x) x - mainTargetR F G W x : ℝ) : ℂ)) =
      (((windowDivisorProduct F G H (W x) (b x) (D x) x : ℝ)) : ℂ) - mainTarget F G W x := by
    rw [Complex.ofReal_sub, mainTarget_eq_ofReal]
  rw [← key, norm_ofReal_complex] at h
  exact h

/-- **The `S₁` bound for the tensor-product sieve weight** (Polymath8a (13)),
**pairwise form**: `Σ_{n ≡ b (W)} ν(n) ≤ (α + o(1))·B^{-k}·x/W` where
`ν = (Σ_j c_j ∏ᵢ λ_{f_{j,i}}(·+Hᵢ))²` and `α = tpAlpha c f`.  Assembled from
`theorem36_i_real` applied to each of the `J²` pairs `(j, j′)`; the errors of the
pairs are combined into a single `ε → 0`.

The hypothesis is only the *pairwise* support condition
`2·(∑ i, max (M j i) (M j′ i)) < 1` (Polymath8a §5.3 (87): for the tensor products
produced by the `ε`-enlargement one only has
`S(f_{1,j}) + ⋯ + S(f_{k,j}) ≤ (1+ε)ϑ/2`, so the per-component bound `ϑ/2` is *not*
available; only pairs with `(1+ε)ϑ < 1` are controlled). -/
theorem weightSum_tpWeight_le_pairwise_sep {k J : ℕ} (hk : 1 ≤ k) (hJ : 1 ≤ J)
    (c : Fin J → ℝ) (f : Fin J → Fin k → ℝ → ℝ) (H : Fin k → ℕ)
    (hHinj : Function.Injective H)
    (hcs : ∀ j i, HasCompactSupport (f j i)) (hsm : ∀ j i, ContDiff ℝ (↑(⊤ : ℕ∞)) (f j i))
    (M : Fin J → Fin k → ℝ) (hMnn : ∀ j i, 0 ≤ M j i)
    (hsupp : ∀ j i t, M j i < |t| → f j i t = 0)
    (hMpair : ∀ j j', (∑ i, (M j i + M j' i)) < 1)
    {Mc : ℝ} (hMc : ∀ j i t, Mc < |t| → f j i t = 0)
    (W : ℕ → ℕ) (hW : ∀ x, W x ≠ 0) (w : ℕ → ℕ) (hw : Tendsto w atTop atTop)
    (hsmall : ∀ x p : ℕ, p.Prime → p ≤ w x → p ∣ W x)
    (hlq : Tendsto (fun x : ℕ => Real.log (W x : ℝ) / Real.sqrt (Real.log (x : ℝ)))
      atTop (𝓝 0))
    (D : ℕ → ℕ) (hD : ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ Mc ≤ (D x : ℝ))
    (b : ℕ → ℕ) (hbW : ∀ x i, (b x + H i).Coprime (W x)) :
    ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ (∀ x, 0 ≤ ε x) ∧
      ∀ x : ℕ, x₀ ≤ x →
      weightSum (W x) (b x) x (fun m => (tpWeight c f x (D x) H m) ^ 2) ≤
        (tpAlpha c f + ε x) * prefOne x (W x) k := by
  classical
  have hpair : ∀ p : Fin J × Fin J,
      ∃ x₀ : ℕ, ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ x : ℕ, x₀ ≤ x →
        |windowDivisorProduct (f p.1) (f p.2) H (W x) (b x) (D x) x -
          mainTargetR (f p.1) (f p.2) (fun _ => W x) x| ≤
          ε x * mainScale k (fun _ => W x) x := by
    intro p
    have hσp : (∑ i, M p.1 i) + (∑ i, M p.2 i) < 1 := by
      have h := hMpair p.1 p.2
      rwa [Finset.sum_add_distrib] at h
    exact theorem36_i_real_sep hk H hHinj (f p.1) (f p.2)
      (fun i => hcs p.1 i) (fun i => hsm p.1 i) (fun i => hcs p.2 i) (fun i => hsm p.2 i)
      (M p.1) (M p.2) (fun i => hMnn p.1 i) (fun i => hMnn p.2 i)
      (fun i t ht => hsupp p.1 i t ht) (fun i t ht => hsupp p.2 i t ht)
      hσp (fun i t ht => ⟨hMc p.1 i t ht, hMc p.2 i t ht⟩)
      W hW w hw hsmall hlq D hD b hbW
  choose x₀p εp hεp using hpair
  refine ⟨max 2 ((Finset.univ : Finset (Fin J × Fin J)).sup'
      ⟨(⟨0, hJ⟩, ⟨0, hJ⟩), Finset.mem_univ _⟩ x₀p),
    (fun x => ∑ p : Fin J × Fin J, |c p.1 * c p.2| * |εp p x|), ?_,
    fun x => Finset.sum_nonneg fun p _ => mul_nonneg (abs_nonneg _) (abs_nonneg _), ?_⟩
  · have hη : ∀ p : Fin J × Fin J, Tendsto (fun x => |εp p x|) atTop (𝓝 (0 : ℝ)) := by
      intro p
      have h := (hεp p).1.abs
      simpa using h
    have hsum_t : Tendsto (fun x => ∑ p ∈ (Finset.univ : Finset (Fin J × Fin J)),
        |c p.1 * c p.2| * |εp p x|) atTop
        (𝓝 (∑ p ∈ (Finset.univ : Finset (Fin J × Fin J)), |c p.1 * c p.2| * 0)) :=
      tendsto_finsetSum _ (fun p _ => tendsto_const_nhds.mul (hη p))
    simpa using hsum_t
  · intro x hx
    have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
    have hx0 : ∀ p : Fin J × Fin J, x₀p p ≤ x := fun p =>
      le_trans (Finset.le_sup' x₀p (Finset.mem_univ p)) (le_trans (le_max_right _ _) hx)
    have hMSpos : 0 < mainScale k (fun _ => W x) x := mainScale_pos (hW x) hx2 k
    have hMSnn : 0 ≤ mainScale k (fun _ => W x) x := le_of_lt hMSpos
    have hεnn_all : ∀ p : Fin J × Fin J, 0 ≤ εp p x := by
      intro p
      have h := (hεp p).2 x (hx0 p)
      have h0 : (0 : ℝ) ≤ εp p x * mainScale k (fun _ => W x) x :=
        le_trans (abs_nonneg _) h
      nlinarith [h0, hMSpos]
    have habsp : ∀ p : Fin J × Fin J,
        |windowDivisorProduct (f p.1) (f p.2) H (W x) (b x) (D x) x -
          mainTargetR (f p.1) (f p.2) (fun _ => W x) x| ≤
          |εp p x| * mainScale k (fun _ => W x) x := by
      intro p
      have h := (hεp p).2 x (hx0 p)
      rw [← abs_of_nonneg (hεnn_all p)] at h
      exact h
    rw [weightSum_tpWeight_sq]
    have hstep1 : (∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
          windowDivisorProduct (f j) (f j') H (W x) (b x) (D x) x) ≤
        ∑ j : Fin J, ∑ j' : Fin J, (c j * c j' *
            mainTargetR (f j) (f j') (fun _ => W x) x +
          |c j * c j'| * (|εp (j, j') x| * mainScale k (fun _ => W x) x)) := by
      refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun j' _ => ?_
      have h2 : c j * c j' *
            (windowDivisorProduct (f j) (f j') H (W x) (b x) (D x) x -
              mainTargetR (f j) (f j') (fun _ => W x) x) ≤
          |c j * c j'| * (|εp (j, j') x| * mainScale k (fun _ => W x) x) := by
        calc c j * c j' *
              (windowDivisorProduct (f j) (f j') H (W x) (b x) (D x) x -
                mainTargetR (f j) (f j') (fun _ => W x) x)
            ≤ |c j * c j' * (windowDivisorProduct (f j) (f j') H (W x) (b x) (D x) x -
                mainTargetR (f j) (f j') (fun _ => W x) x)| := le_abs_self _
          _ = |c j * c j'| * |windowDivisorProduct (f j) (f j') H (W x) (b x) (D x) x -
                mainTargetR (f j) (f j') (fun _ => W x) x| := abs_mul _ _
          _ ≤ |c j * c j'| * (|εp (j, j') x| * mainScale k (fun _ => W x) x) :=
              mul_le_mul_of_nonneg_left (habsp (j, j')) (abs_nonneg _)
      linarith
    refine le_trans hstep1 ?_
    simp only [Finset.sum_add_distrib]
    have hfirst : (∑ j : Fin J, ∑ j' : Fin J, c j * c j' *
          mainTargetR (f j) (f j') (fun _ => W x) x) =
        mainScale k (fun _ => W x) x * tpAlpha c f := by
      rw [tpAlpha]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
      rw [mainTargetR]
      ring
    have hsecond : (∑ j : Fin J, ∑ j' : Fin J, |c j * c j'| *
          (|εp (j, j') x| * mainScale k (fun _ => W x) x)) =
        (∑ j : Fin J, ∑ j' : Fin J, |c j * c j'| * |εp (j, j') x|) *
          mainScale k (fun _ => W x) x := by
      simp only [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
      ring
    rw [hfirst, hsecond, ← prefOne_eq_mainScale, Fintype.sum_prod_type]
    exact le_of_eq (by ring)

end Commons.NumberTheory.MaynardSieve
