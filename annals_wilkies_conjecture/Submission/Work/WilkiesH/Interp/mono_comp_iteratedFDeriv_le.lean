import Mathlib
import Submission.Work.WilkiesH.Interp.JetSetup
import Submission.Work.WilkiesH.Interp.jet_prod_bound

namespace Work.WilkiesH.Interp

open Work.WilkiesH

/-- The open unit cube `(0,1)^μ` is an open subset of `Fin μ → ℝ`. -/
lemma isOpen_openCube (μ : ℕ) : IsOpen (WilkiesDesign.openCube μ) := by
  have h : WilkiesDesign.openCube μ = Set.pi Set.univ (fun _ : Fin μ => Set.Ioo (0 : ℝ) 1) := by
    ext t; simp [WilkiesDesign.openCube]
  rw [h]
  exact isOpen_set_pi Set.finite_univ (fun i _ => isOpen_Ioo)

/-- Projecting a map to one of its coordinates does not increase the norm of any jet: the
coordinate map is `L ∘ φ` for the linear projection `L` of operator norm `≤ 1`. -/
lemma proj_iteratedFDeriv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {φ : E → (Fin k → ℝ)} {x : E} {r j : ℕ} (i : Fin k)
    (hφ : ContDiffAt ℝ r φ x) (hj : j ≤ r) :
    ‖iteratedFDeriv ℝ j (fun y => φ y i) x‖ ≤ ‖iteratedFDeriv ℝ j φ x‖ := by
  let L : (Fin k → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i
  have hL : ‖L‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound L zero_le_one (fun v => by
      rw [one_mul]
      exact norm_le_pi_norm v i)
  have hcomp : iteratedFDeriv ℝ j (fun y => φ y i) x
      = L.compContinuousMultilinearMap (iteratedFDeriv ℝ j φ x) :=
    ContinuousLinearMap.iteratedFDeriv_comp_left L hφ (by exact_mod_cast hj)
  calc ‖iteratedFDeriv ℝ j (fun y => φ y i) x‖
      = ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ j φ x)‖ := by rw [hcomp]
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ j φ x‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le L _
    _ ≤ 1 * ‖iteratedFDeriv ℝ j φ x‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ j φ x‖ := one_mul _

/-- Jet bound for a product indexed by an arbitrary finite set: if every factor is `C^j` at `x`
with values bounded by `1` and jets of positive order bounded by `1`, then the `j`-th jet of the
product is bounded by `(card) ^ j`.  This is `norm_prod_le` transported along `Finset.equivFin`. -/
lemma finset_prod_iteratedFDeriv_le {m j : ℕ} {ι : Type*} (s : Finset ι)
    (g : ι → (Fin m → ℝ) → ℝ) (x : Fin m → ℝ)
    (hdiff : ∀ i ∈ s, ContDiffAt ℝ (j : ℕ) (g i) x)
    (hval : ∀ i ∈ s, |g i x| ≤ 1)
    (hjet : ∀ i ∈ s, ∀ k, 1 ≤ k → k ≤ j → ‖iteratedFDeriv ℝ k (g i) x‖ ≤ 1) :
    ‖iteratedFDeriv ℝ j (fun y => ∏ i ∈ s, g i y) x‖ ≤ (s.card : ℝ) ^ j := by
  classical
  set e : s ≃ Fin s.card := Finset.equivFin s with he
  set g' : Fin s.card → (Fin m → ℝ) → ℝ := fun k => g (e.symm k : ι) with hg'
  have hfun : (fun y => ∏ i ∈ s, g i y) = fun y => ∏ k : Fin s.card, g' k y := by
    funext y
    rw [← Finset.prod_attach s (fun i => g i y)]
    rw [show (∏ k : Fin s.card, g' k y) = ∏ i : s, g (i : ι) y from by
      rw [hg']
      exact Fintype.prod_equiv e.symm (fun k : Fin s.card => g (e.symm k : ι) y)
        (fun i : s => g (i : ι) y) (fun k => rfl)]
    simp
  rw [hfun]
  exact norm_prod_le g' x
    (fun k => by simpa only [hg'] using hdiff (e.symm k : ι) (e.symm k).2)
    (fun k => by simpa only [hg'] using hval (e.symm k : ι) (e.symm k).2)
    (fun k n hn1 hnj => by simpa only [hg'] using hjet (e.symm k : ι) (e.symm k).2 n hn1 hnj)

/-- **Jet bound for a monomial composed with a chart.**  If `γ` is an exponent vector of total
degree `≤ d` and `ψ : (Fin μ → ℝ) → (Fin (μ+1) → ℝ)` has all its jets of order `≤ b` bounded by
`1` and all its values bounded by `1` on the open cube, then the `j`-th jet (`j ≤ b`) of the
monomial `mono γ` composed with `ψ` is bounded by `d ^ j` at every point `t₀` of the open cube.

Intended proof: write `mono γ ∘ ψ = ∏_{p : Σ i : Fin (μ+1), Fin (γ.toFun i)} ψ (p.1)` (a product of
`∑ i, γ.toFun i ≤ d` coordinate functions) and apply Mathlib's multilinear Leibniz bound
`norm_iteratedFDeriv_prod_le`; the multinomial coefficients sum to `(card)^j ≤ d^j` by
`Multiset.countPerms` / `Finset.sum_sym`-type identities, and every factor is bounded by `1`
(jet bound for positive orders, `hψval` for order `0`). -/
theorem mono_comp_iteratedFDeriv_le {μ b d : ℕ} (γ : Work.WilkiesH.ExpVec (μ + 1) d)
    {ψ : (Fin μ → ℝ) → (Fin (μ + 1) → ℝ)} {t₀ : Fin μ → ℝ}
    (hψ : ContDiffOn ℝ (b + 1 : ℕ) ψ (WilkiesDesign.openCube μ))
    (ht₀ : t₀ ∈ WilkiesDesign.openCube μ)
    (hψjet : ∀ k, k ≤ b → ∀ t ∈ WilkiesDesign.openCube μ, ‖iteratedFDeriv ℝ k ψ t‖ ≤ 1)
    (hψval : ∀ t ∈ WilkiesDesign.openCube μ, ∀ i, |ψ t i| ≤ 1)
    {j : ℕ} (hj : j ≤ b) :
    ‖iteratedFDeriv ℝ j (fun s => (Work.WilkiesH.ExpVec.mono γ).eval (ψ s)) t₀‖
      ≤ (d : ℝ) ^ j := by
  classical
  -- `openCube μ` is open, so being `C^{b+1}` on it gives `C^{b+1}` (hence `C^j`) at `t₀`.
  have hopen : IsOpen (WilkiesDesign.openCube μ) := isOpen_openCube μ
  have hψat : ContDiffAt ℝ (b + 1 : ℕ) ψ t₀ := hψ.contDiffAt (hopen.mem_nhds ht₀)
  have hψjat : ContDiffAt ℝ (j : ℕ) ψ t₀ := hψat.of_le (by exact_mod_cast Nat.le_succ_of_le hj)
  -- every coordinate `s ↦ ψ s i` is `C^j` at `t₀` and has value and jets bounded by `1`.
  have hcoord_diff : ∀ i : Fin (μ + 1), ContDiffAt ℝ (j : ℕ) (fun s => ψ s i) t₀ := by
    intro i
    exact ContDiffAt.comp t₀
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (μ + 1) => ℝ) i).contDiff.contDiffAt)
      hψjat
  have hcoord_jet : ∀ i : Fin (μ + 1), ∀ k, 1 ≤ k → k ≤ j →
      ‖iteratedFDeriv ℝ k (fun s => ψ s i) t₀‖ ≤ 1 := by
    intro i k _ hkj
    exact (proj_iteratedFDeriv_le i hψat
        (by exact_mod_cast Nat.le_succ_of_le (le_trans hkj hj))).trans
      (hψjet k (le_trans hkj hj) t₀ ht₀)
  -- the monomial is the product of `∑ i, γ.toFun i` copies of the coordinate functions, indexed
  -- by the sigma type of the exponent vector.
  let ι := Sigma (fun i : Fin (μ + 1) => Fin (γ.toFun i))
  have hcard : Fintype.card ι = ∑ i, γ.toFun i := by
    simp only [ι, Fintype.card_sigma, Fintype.card_fin]
  have hfun : (fun s => ∏ p : ι, ψ s p.1) = fun s => ∏ i, (ψ s i) ^ γ.toFun i := by
    funext s
    rw [Fintype.prod_sigma (f := fun p : ι => ψ s p.1)]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [show (∏ y : Fin (γ.toFun i), ψ s (⟨i, y⟩ : ι).1)
          = ∏ _y : Fin (γ.toFun i), ψ s i from
      Finset.prod_congr rfl (fun y _ => rfl)]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hmono : (fun s => (Work.WilkiesH.ExpVec.mono γ).eval (ψ s))
      = fun s => ∏ i, (ψ s i) ^ γ.toFun i := by
    funext s
    change Work.WilkiesH.ExpVec.eval γ (ψ s) = ∏ i, (ψ s) i ^ γ.toFun i
    rw [Work.WilkiesH.ExpVec.eval_eq_prod]
  -- apply the product bound to the `∑ i, γ.toFun i` coordinate factors.
  have hmain := finset_prod_iteratedFDeriv_le (s := (Finset.univ : Finset ι))
    (g := fun p : ι => fun s => ψ s p.1) t₀
    (fun p _ => hcoord_diff p.1)
    (fun p _ => hψval t₀ ht₀ p.1)
    (fun p _ k hk1 hkj => hcoord_jet p.1 k hk1 hkj)
  rw [Finset.card_univ, hcard] at hmain
  calc ‖iteratedFDeriv ℝ j (fun s => (Work.WilkiesH.ExpVec.mono γ).eval (ψ s)) t₀‖
      = ‖iteratedFDeriv ℝ j (fun s => ∏ p : ι, ψ s p.1) t₀‖ := by rw [hmono, hfun]
    _ ≤ ((∑ i, γ.toFun i : ℕ) : ℝ) ^ j := hmain
    _ ≤ (d : ℝ) ^ j :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast γ.toFun_sum_le) j

end Work.WilkiesH.Interp
