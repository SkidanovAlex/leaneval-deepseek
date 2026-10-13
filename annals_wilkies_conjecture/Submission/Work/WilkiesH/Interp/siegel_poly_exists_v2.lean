import Mathlib
import Submission.Work.WilkiesH.Defs
import Submission.Work.WilkiesH.NT.siegel_approx
import Submission.Work.WilkiesH.Interp.JetSetup
import Submission.Work.WilkiesH.Interp.fiberJet_linear
import Submission.Work.WilkiesH.Interp.sum_fiberCard_weight
import Submission.Work.WilkiesH.Interp.diag_fiberSum_expansion
import Submission.Work.WilkiesH.Interp.mono_comp_iteratedFDeriv_le

/-!
# The Siegel–Wilkie polynomial of the interpolation step (`v2`, with the `√monoCount` factor)

This file proves `Work.WilkiesH.Interp.siegel_poly_exists_v2`: the existence, for a `C^{b+1}` chart
`ψ : (Fin μ → ℝ) → (Fin (μ+1) → ℝ)` with jets bounded by `1` on the open cube, of a nonzero
integral polynomial `P` of degree `≤ d` and coefficients bounded by `Q` whose *jets* at `t₀`
of all orders `j ≤ b` are bounded by `√N · μ^j ρ^{b-j} d^j ‖v‖^j` (`N = monoCount (μ+1) d`).

The proof is the one of `siegel_poly_exists` (Siegel–Wilkie with a jet matrix); the only changes
are that the two auxiliary inputs are taken from the sorry-free modules
`Interp.diag_fiberSum_expansion` and `Interp.mono_comp_iteratedFDeriv_le`, and that the final
numerical step uses `1 ≤ √N ≤ N` in place of `1 ≤ N`, so that the conclusion carries the
weaker factor `√N`.

The rows of the "jet matrix" are indexed by the exponent vectors `α : ExpVec μ b` (the monomials
of degree `≤ b` in `μ` variables) and the columns by the monomials `γ : ExpVec (μ+1) d`; the entry
at `(α, γ)` is, up to the row scale `B / (#fiber α · d^{|α|})`, the *fiber sum*
`∑_{g : mult(g) = α} (D^{|α|} (mono γ ∘ ψ) t₀)(e_{g 1}, …)`, where `mult(g) = α` means that the
tuple `g : Fin |α| → Fin μ` has multiplicity vector `α`.  Siegel's lemma (`NT.siegel_approx`)
produces a nonzero integer vector `x` with `|x| ≤ Q` and `|A x| ≤ 1`.  The conclusion then uses

* the *multilinear expansion of the diagonal*
  `(D^n F t₀)(v, …, v) = ∑_α (∏ i, v i ^ α i) · (fiber sum of D^n F t₀ over α)`, and
* the *weighted fiber count* `∑_α (∏ i, w i ^ α i) · #(fiber α) = (∑ i, w i)^n`,

which turn the row bounds into `(d^n/B) · (∑ i, |v i|)^n ≤ (d^n/B)(μ ‖v‖)^n`, while
`1/B ≤ ρ^{b-n}` because `B = ⌈ρ^{-b}⌉ ≥ ρ^{-b}` and `ρ ≤ 1`.
-/

set_option autoImplicit false

namespace Work.WilkiesH.Interp

open Work.WilkiesH

/-- The tuples of length `n` with multiplicity vector `α` form an empty type when the
multiplicities do not add up to `n`. -/
private lemma isEmpty_jetFiber {μ n : ℕ} {α : Fin μ → ℕ} (h : (∑ i, α i) ≠ n) :
    IsEmpty {g : Fin n → Fin μ // ∀ i, Fintype.card {l : Fin n // g l = i} = α i} :=
  ⟨fun g => h (by
    have h1 : (∑ i, α i) = ∑ i, multFun g.1 i :=
      Finset.sum_congr rfl (fun i _ => by rw [multFun_eq_card]; exact (g.2 i).symm)
    rw [h1, sum_multFun])⟩

private lemma jetFiberSum_eq_zero_of_ne {μ n : ℕ} {α : Fin μ → ℕ} {F : (Fin μ → ℝ) → ℝ}
    {t₀ : Fin μ → ℝ} (h : (∑ i, α i) ≠ n) : jetFiberSum n α F t₀ = 0 := by
  haveI := isEmpty_jetFiber h
  rw [jetFiberSum, Finset.univ_eq_empty, Finset.sum_empty]

private lemma jetFiberCard_eq_zero_of_ne {μ n : ℕ} {α : Fin μ → ℕ} (h : (∑ i, α i) ≠ n) :
    jetFiberCard μ n α = 0 :=
  Fintype.card_eq_zero_iff.mpr (isEmpty_jetFiber h)

private lemma jetFiberSum_eq_zero_of_card_eq_zero {μ n : ℕ} {α : Fin μ → ℕ}
    {F : (Fin μ → ℝ) → ℝ} {t₀ : Fin μ → ℝ} (h : jetFiberCard μ n α = 0) :
    jetFiberSum n α F t₀ = 0 := by
  haveI : IsEmpty {g : Fin n → Fin μ // ∀ i, Fintype.card {l : Fin n // g l = i} = α i} :=
    Fintype.card_eq_zero_iff.mp h
  rw [jetFiberSum, Finset.univ_eq_empty, Finset.sum_empty]

/-- A jet fiber sum is bounded by the cardinality of the fiber times a jet bound. -/
private lemma abs_jetFiberSum_le {μ : ℕ} (m : ℕ) (α : Fin μ → ℕ) (G : (Fin μ → ℝ) → ℝ)
    (t₀ : Fin μ → ℝ) {C : ℝ} (hG : ‖iteratedFDeriv ℝ m G t₀‖ ≤ C) :
    |jetFiberSum m α G t₀| ≤ (jetFiberCard μ m α : ℝ) * C := by
  have hsum : |jetFiberSum m α G t₀|
      ≤ ∑ _g : {g : Fin m → Fin μ // ∀ i, Fintype.card {l : Fin m // g l = i} = α i},
          ‖iteratedFDeriv ℝ m G t₀‖ := by
    rw [jetFiberSum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun g _ => ?_)
    let w : Fin m → (Fin μ → ℝ) := fun k => Pi.single (g.1 k) (1 : ℝ)
    show |(iteratedFDeriv ℝ m G t₀) w| ≤ ‖iteratedFDeriv ℝ m G t₀‖
    calc |(iteratedFDeriv ℝ m G t₀) w|
        = ‖(iteratedFDeriv ℝ m G t₀) w‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖iteratedFDeriv ℝ m G t₀‖ * ∏ k : Fin m, ‖w k‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ m G t₀‖ := by simp only [w, Pi.norm_single, norm_one,
            Finset.prod_const_one, mul_one]
  calc |jetFiberSum m α G t₀|
      ≤ ∑ _g : {g : Fin m → Fin μ // ∀ i, Fintype.card {l : Fin m // g l = i} = α i},
          ‖iteratedFDeriv ℝ m G t₀‖ := hsum
    _ = (jetFiberCard μ m α : ℝ) * ‖iteratedFDeriv ℝ m G t₀‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rfl
    _ ≤ (jetFiberCard μ m α : ℝ) * C := mul_le_mul_of_nonneg_left hG (Nat.cast_nonneg _)

/-- Smoothness of a monomial composed with the chart. -/
private lemma contDiffAt_mono_comp {μ d : ℕ} (γ : ExpVec (μ + 1) d)
    {ψ : (Fin μ → ℝ) → (Fin (μ + 1) → ℝ)} {t₀ : Fin μ → ℝ} {n : ℕ}
    (hψ : ContDiffAt ℝ n ψ t₀) :
    ContDiffAt ℝ n (fun s => (ExpVec.mono γ).eval (ψ s)) t₀ := by
  rw [show (fun s => (ExpVec.mono γ).eval (ψ s)) = fun s => ∏ i, (ψ s) i ^ γ.toFun i from
    funext (fun s => ExpVec.eval_eq_prod γ (ψ s))]
  fun_prop

/-- The `mono`-monomials have injective exponent vectors. -/
private lemma toFinsupp_injective {n d : ℕ} :
    Function.Injective (fun α : ExpVec n d => ExpVec.toFinsupp α) := by
  intro a b hab
  have h1 : ∀ i, a.toFun i = b.toFun i := fun i => by
    rw [← ExpVec.toFinsupp_apply a i, ← ExpVec.toFinsupp_apply b i]
    exact (Finsupp.ext_iff.mp hab) i
  exact Subtype.ext (funext fun i => Fin.ext (h1 i))

/-- Evaluation of a monomial with a coefficient. -/
private lemma eval_monomial_eq {n d : ℕ} (γ : ExpVec n d) (a : ℝ) (x : Fin n → ℝ) :
    (MvPolynomial.monomial (ExpVec.toFinsupp γ) a).eval x = a * ExpVec.eval γ x := by
  have h : MvPolynomial.monomial (ExpVec.toFinsupp γ) a
      = MvPolynomial.C a * ExpVec.mono γ := by
    rw [ExpVec.mono, MvPolynomial.C_mul_monomial, mul_one]
  rw [h, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  rfl

/-- Auxiliary form of `siegel_poly_exists_v2` with the numerical abbreviations as variables. -/
private theorem siegel_poly_aux_v2 {μ b d Q : ℕ} (_hb : 1 ≤ b) (hd : 1 ≤ d) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (_hQ : 1 ≤ Q)
    {ψ : (Fin μ → ℝ) → (Fin (μ + 1) → ℝ)}
    (hψ : ContDiffOn ℝ (b + 1 : ℕ) ψ (WilkiesDesign.openCube μ))
    (hψjet : ∀ k, k ≤ b → ∀ t ∈ WilkiesDesign.openCube μ, ‖iteratedFDeriv ℝ k ψ t‖ ≤ 1)
    (hψval : ∀ t ∈ WilkiesDesign.openCube μ, ∀ i, |ψ t i| ≤ 1)
    {t₀ : Fin μ → ℝ} (ht₀ : t₀ ∈ WilkiesDesign.openCube μ)
    {N M Bn : ℕ} {B : ℝ} (hN : N = monoCount (μ + 1) d) (hM : M = monoCount μ b)
    (hB : B = (Bn : ℝ)) (hBn : Bn = Nat.ceil (ρ ^ (-(b : ℤ))))
    (hcard : (Q + 1) ^ N > (2 * (N * Bn * Q) + 1) ^ M) :
    ∃ P : MvPolynomial (Fin (μ + 1)) ℤ, P ≠ 0 ∧ P.totalDegree ≤ d ∧
      (∀ m ∈ P.support, |(P.coeff m : ℤ)| ≤ (Q : ℤ)) ∧
      ∀ j, j ≤ b → ∀ v : Fin μ → ℝ,
        |iteratedFDeriv ℝ j (fun s => (P.map (Int.castRingHom ℝ)).eval (ψ s)) t₀
            (fun _ => v)|
          ≤ ((μ : ℝ) ^ j * ρ ^ (b - j) * Real.sqrt (N : ℝ) * (d : ℝ) ^ j) * ‖v‖ ^ j := by
  classical
  -- ## numerical preliminaries
  have hBz_pos : 0 < ρ ^ (-(b : ℤ)) := zpow_pos hρ _
  have hBn_pos : 0 < Bn := by rw [hBn]; exact Nat.ceil_pos.mpr hBz_pos
  have hB_pos : 0 < B := by rw [hB]; exact_mod_cast hBn_pos
  have hB_nn : 0 ≤ B := le_of_lt hB_pos
  have hBz : ρ ^ (-(b : ℤ)) = (ρ ^ b)⁻¹ := by rw [zpow_neg, zpow_natCast]
  have hle_B : (ρ ^ b)⁻¹ ≤ B := by
    rw [hB, hBn, ← hBz]
    exact Nat.le_ceil _
  have hρb_pos : 0 < ρ ^ b := pow_pos hρ b
  have hinvB : 1 / B ≤ ρ ^ b := by
    rw [div_le_iff₀ hB_pos]
    have h := mul_le_mul_of_nonneg_left hle_B (le_of_lt hρb_pos)
    simpa only [mul_inv_cancel₀ (ne_of_gt hρb_pos)] using h
  have hN1 : 1 ≤ N := by
    rw [hN]
    show 1 ≤ Fintype.card (ExpVec (μ + 1) d)
    exact Fintype.card_pos_iff.mpr ⟨⟨fun _ => 0, by simp⟩⟩
  have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  -- the v2-specific ingredient: `1 ≤ √N` (used in place of `1 ≤ N` at the very end)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := Real.one_le_sqrt.mpr hN1'
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  -- the open cube is open
  have hopenCube : IsOpen (WilkiesDesign.openCube μ) := by
    have h : WilkiesDesign.openCube μ = Set.pi Set.univ (fun _ : Fin μ => Set.Ioo (0 : ℝ) 1) := by
      ext t
      simp [WilkiesDesign.openCube]
    rw [h]
    exact isOpen_set_pi Set.finite_univ (fun i _ => isOpen_Ioo)
  have hψAt : ContDiffAt ℝ (b + 1 : ℕ) ψ t₀ := hψ.contDiffAt (hopenCube.mem_nhds ht₀)
  -- ## the jet matrix
  have hcardM : Fintype.card (ExpVec μ b) = M := by rw [hM]; rfl
  have hcardN : Fintype.card (ExpVec (μ + 1) d) = N := by rw [hN]; rfl
  let eα : Fin M ≃ ExpVec μ b := (Fintype.equivFinOfCardEq hcardM).symm
  let eγ : Fin N ≃ ExpVec (μ + 1) d := (Fintype.equivFinOfCardEq hcardN).symm
  let Gf : ExpVec (μ + 1) d → (Fin μ → ℝ) → ℝ := fun γ s => (ExpVec.mono γ).eval (ψ s)
  let sc : ExpVec μ b → ℝ := fun α =>
    B / ((jetFiberCard μ (∑ i, α.toFun i) α.toFun : ℝ) * (d : ℝ) ^ (∑ i, α.toFun i))
  let A : Matrix (Fin M) (Fin N) ℝ := fun i j =>
    sc (eα i) * jetFiberSum (∑ i', (eα i).toFun i') (eα i).toFun (Gf (eγ j)) t₀
  -- the entries of the jet matrix are bounded by `B`
  have hA : ∀ i j, |A i j| ≤ B := by
    intro i j
    have hjet : ‖iteratedFDeriv ℝ (∑ i', (eα i).toFun i') (Gf (eγ j)) t₀‖
        ≤ (d : ℝ) ^ (∑ i', (eα i).toFun i') :=
      mono_comp_iteratedFDeriv_le (eγ j) hψ ht₀ hψjet hψval (eα i).prop
    have hbnd := abs_jetFiberSum_le (∑ i', (eα i).toFun i') (eα i).toFun (Gf (eγ j)) t₀ hjet
    show |sc (eα i) * jetFiberSum (∑ i', (eα i).toFun i') (eα i).toFun (Gf (eγ j)) t₀| ≤ B
    by_cases hc : jetFiberCard μ (∑ i', (eα i).toFun i') (eα i).toFun = 0
    · have hz : jetFiberSum (∑ i', (eα i).toFun i') (eα i).toFun (Gf (eγ j)) t₀ = 0 :=
        jetFiberSum_eq_zero_of_card_eq_zero hc
      rw [hz, mul_zero, abs_zero]
      exact hB_nn
    · have hcpos : (0 : ℝ) < (jetFiberCard μ (∑ i', (eα i).toFun i') (eα i).toFun : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hc
      have hden : 0 < (jetFiberCard μ (∑ i', (eα i).toFun i') (eα i).toFun : ℝ)
          * (d : ℝ) ^ (∑ i', (eα i).toFun i') := by positivity
      have hsc_nn : 0 ≤ sc (eα i) := by
        show 0 ≤ B / _
        exact div_nonneg hB_nn (le_of_lt hden)
      calc |sc (eα i) * jetFiberSum (∑ i', (eα i).toFun i') (eα i).toFun (Gf (eγ j)) t₀|
          = sc (eα i) * |jetFiberSum (∑ i', (eα i).toFun i') (eα i).toFun (Gf (eγ j)) t₀| := by
            rw [abs_mul, abs_of_nonneg hsc_nn]
        _ ≤ sc (eα i) * ((jetFiberCard μ (∑ i', (eα i).toFun i') (eα i).toFun : ℝ)
              * (d : ℝ) ^ (∑ i', (eα i).toFun i')) := mul_le_mul_of_nonneg_left hbnd hsc_nn
        _ = B := by
            show B / _ * _ = B
            exact div_mul_cancel₀ B (ne_of_gt hden)
  -- ## Siegel's lemma
  have hK : (N : ℝ) * B * Q ≤ ((N * Bn * Q : ℕ) : ℝ) := by
    rw [hB]
    push_cast
    ring_nf
    exact le_refl _
  obtain ⟨x, hxne, hxQ, hxA⟩ :=
    NT.siegel_approx (M := M) (N := N) (B := B) A hB_nn hA Q (N * Bn * Q) hK hcard
  -- ## the polynomial
  let vp : ExpVec (μ + 1) d → ℤ := fun γ => x (eγ.symm γ)
  let P : MvPolynomial (Fin (μ + 1)) ℤ :=
    ∑ γ : ExpVec (μ + 1) d, MvPolynomial.monomial (ExpVec.toFinsupp γ) (vp γ)
  let Fsum : (Fin μ → ℝ) → ℝ := fun s => ∑ γ : ExpVec (μ + 1) d,
    ((vp γ : ℤ) : ℝ) * ExpVec.eval γ (ψ s)
  have hPa : ∀ γ : ExpVec (μ + 1) d, P.coeff (ExpVec.toFinsupp γ) = vp γ := by
    intro γ
    show (∑ γ' : ExpVec (μ + 1) d,
        MvPolynomial.monomial (ExpVec.toFinsupp γ') (vp γ')).coeff (ExpVec.toFinsupp γ) = vp γ
    rw [MvPolynomial.coeff_sum]
    refine (Finset.sum_eq_single γ ?_ ?_).trans ?_
    · intro γ' _ hne
      rw [MvPolynomial.coeff_monomial]
      by_cases h : ExpVec.toFinsupp γ' = ExpVec.toFinsupp γ
      · exact absurd (toFinsupp_injective h) hne
      · simp [h]
    · intro hnot
      exact absurd (Finset.mem_univ γ) hnot
    · rw [MvPolynomial.coeff_monomial]
      simp
  have hmapP : P.map (Int.castRingHom ℝ)
      = ∑ γ : ExpVec (μ + 1) d,
          MvPolynomial.monomial (ExpVec.toFinsupp γ) (((vp γ : ℤ) : ℝ)) := by
    show (∑ γ : ExpVec (μ + 1) d,
        MvPolynomial.monomial (ExpVec.toFinsupp γ) (vp γ)).map (Int.castRingHom ℝ) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun γ _ => MvPolynomial.map_monomial _ _ _
  have hPfun : (fun s : Fin μ → ℝ => (P.map (Int.castRingHom ℝ)).eval (ψ s)) = Fsum := by
    funext s
    rw [hmapP, MvPolynomial.eval_sum]
    exact Finset.sum_congr rfl fun γ _ => eval_monomial_eq γ _ (ψ s)
  -- ## `fiberJet_linear`: the row sums are the fiber sums of `Fsum`
  have hidentM : ∀ α : ExpVec μ b,
      jetFiberSum (∑ i, α.toFun i) α.toFun Fsum t₀
        = ∑ γ : ExpVec (μ + 1) d, ((vp γ : ℤ) : ℝ)
            * jetFiberSum (∑ i, α.toFun i) α.toFun (Gf γ) t₀ := by
    intro α
    exact fiberJet_linear (μ := μ) (k := μ + 1) (d := d) (n := ∑ i, α.toFun i)
      α.toFun rfl t₀ ψ
      (fun γ => contDiffAt_mono_comp γ
        (hψAt.of_le (by exact_mod_cast (le_trans α.prop (Nat.le_succ b)))))
      (fun γ => ((vp γ : ℤ) : ℝ))
  -- ## Step X: the Siegel row bound at the arity `∑ i, α.toFun i`
  have hX : ∀ α : ExpVec μ b, |jetFiberSum (∑ i, α.toFun i) α.toFun Fsum t₀|
      ≤ (jetFiberCard μ (∑ i, α.toFun i) α.toFun : ℝ)
          * (d : ℝ) ^ (∑ i, α.toFun i) / B := by
    intro α
    have hval := hxA (eα.symm α)
    have hrewrite : (∑ j : Fin N, A (eα.symm α) j * ((x j : ℤ) : ℝ))
        = sc α * jetFiberSum (∑ i, α.toFun i) α.toFun Fsum t₀ := by
      rw [hidentM α, Finset.mul_sum]
      refine Fintype.sum_equiv eγ _ _ (fun j => ?_)
      simp only [A, sc, Gf, vp, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
      ring
    rw [hrewrite] at hval
    by_cases hc0 : jetFiberCard μ (∑ i, α.toFun i) α.toFun = 0
    · have hz : jetFiberSum (∑ i, α.toFun i) α.toFun Fsum t₀ = 0 :=
        jetFiberSum_eq_zero_of_card_eq_zero hc0
      rw [hz, abs_zero, hc0]
      simp
    · have hsc_pos : 0 < sc α := by
        show 0 < B / _
        have : (0 : ℝ) < (jetFiberCard μ (∑ i, α.toFun i) α.toFun : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hc0
        positivity
      have h2 : |jetFiberSum (∑ i, α.toFun i) α.toFun Fsum t₀| * sc α ≤ 1 := by
        rw [mul_comm]
        calc sc α * |jetFiberSum (∑ i, α.toFun i) α.toFun Fsum t₀|
            = |sc α * jetFiberSum (∑ i, α.toFun i) α.toFun Fsum t₀| := by
              rw [abs_mul, abs_of_pos hsc_pos]
          _ ≤ 1 := hval
      have h3 : |jetFiberSum (∑ i, α.toFun i) α.toFun Fsum t₀| ≤ 1 / sc α := by
        rw [le_div_iff₀ hsc_pos]
        exact h2
      have h4 : 1 / sc α
          = (jetFiberCard μ (∑ i, α.toFun i) α.toFun : ℝ)
              * (d : ℝ) ^ (∑ i, α.toFun i) / B := by
        show 1 / (B / _) = _
        rw [one_div_div]
      rw [h4] at h3
      exact h3
  -- ## Step Y (for a fixed `j ≤ b`): the row bound at arity `j`
  have hY : ∀ j, j ≤ b → ∀ α : ExpVec μ b, |jetFiberSum j α.toFun Fsum t₀|
      ≤ (jetFiberCard μ j α.toFun : ℝ) * (d : ℝ) ^ j / B := by
    intro j _ α
    by_cases hαj : (∑ i, α.toFun i) = j
    · have h1 := hX α
      rw [jetFiberSum_congr_arity hαj α.toFun Fsum t₀,
        jetFiberCard_congr_arity hαj α.toFun, hαj] at h1
      exact h1
    · have hz : jetFiberSum j α.toFun Fsum t₀ = 0 :=
        jetFiberSum_eq_zero_of_ne (α := α.toFun) (n := j) hαj
      have hc0 : jetFiberCard μ j α.toFun = 0 :=
        jetFiberCard_eq_zero_of_ne (α := α.toFun) (n := j) hαj
      rw [hz, abs_zero, hc0]
      simp
  -- ## the diagonal expansion and the conclusion
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · -- `P ≠ 0`
    intro hPzero
    obtain ⟨j, hj⟩ : ∃ j : Fin N, x j ≠ 0 := by
      by_contra hcon
      apply hxne
      funext j
      by_contra hj
      exact hcon ⟨j, hj⟩
    have hv : vp (eγ j) ≠ 0 := by
      show x (eγ.symm (eγ j)) ≠ 0
      rw [Equiv.symm_apply_apply]
      exact hj
    have hco := hPa (eγ j)
    rw [hPzero] at hco
    have hco' : vp (eγ j) = 0 := by simpa using hco.symm
    exact hv hco'
  · -- the degree bound
    show (∑ γ : ExpVec (μ + 1) d,
        MvPolynomial.monomial (ExpVec.toFinsupp γ) (vp γ)).totalDegree ≤ d
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
    refine Finset.sup_le fun γ _ => ?_
    refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
    have hsum : (ExpVec.toFinsupp γ).sum (fun x => id) = ∑ i, γ.toFun i :=
      ExpVec.sum_toFinsupp γ
    rw [hsum]
    exact γ.prop
  · -- the coefficient bound
    intro m _
    have hcoeff : P.coeff m = ∑ γ ∈ (Finset.univ.filter fun γ : ExpVec (μ + 1) d =>
        ExpVec.toFinsupp γ = m), vp γ := by
      show (∑ γ : ExpVec (μ + 1) d,
        MvPolynomial.monomial (ExpVec.toFinsupp γ) (vp γ)).coeff m = _
      rw [MvPolynomial.coeff_sum, Finset.sum_filter]
      exact Finset.sum_congr rfl fun γ _ => by rw [MvPolynomial.coeff_monomial]
    have hcard1 : (Finset.univ.filter fun γ : ExpVec (μ + 1) d =>
        ExpVec.toFinsupp γ = m).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact toFinsupp_injective (ha.trans hb.symm)
    calc |(P.coeff m : ℤ)| = |∑ γ ∈ (Finset.univ.filter fun γ : ExpVec (μ + 1) d =>
            ExpVec.toFinsupp γ = m), vp γ| := by rw [hcoeff]
      _ ≤ ∑ γ ∈ (Finset.univ.filter fun γ : ExpVec (μ + 1) d =>
            ExpVec.toFinsupp γ = m), |vp γ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _γ ∈ (Finset.univ.filter fun γ : ExpVec (μ + 1) d =>
            ExpVec.toFinsupp γ = m), (Q : ℤ) := by
          refine Finset.sum_le_sum fun γ _ => ?_
          show |x (eγ.symm γ)| ≤ _
          exact hxQ (eγ.symm γ)
      _ = ((Finset.univ.filter fun γ : ExpVec (μ + 1) d =>
            ExpVec.toFinsupp γ = m).card : ℤ) * Q := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * Q := by
          refine mul_le_mul_of_nonneg_right ?_ (by exact_mod_cast Nat.zero_le Q)
          exact_mod_cast hcard1
      _ = Q := one_mul _
  · -- the jet bound
    intro j hj v
    have hdiag := diag_fiberSum_expansion hj Fsum t₀ v
    rw [hPfun, hdiag]
    have hsum_le : (∑ i : Fin μ, |v i|) ≤ (μ : ℝ) * ‖v‖ := by
      calc ∑ i : Fin μ, |v i| ≤ ∑ _i : Fin μ, ‖v‖ := Finset.sum_le_sum fun i _ => by
            rw [← Real.norm_eq_abs]
            exact norm_le_pi_norm v i
        _ = (μ : ℝ) * ‖v‖ := by simp [Finset.sum_const, nsmul_eq_mul]
    have hρpow : ρ ^ b ≤ ρ ^ (b - j) := by
      calc ρ ^ b = ρ ^ (b - j) * ρ ^ j := by rw [← pow_add, Nat.sub_add_cancel hj]
        _ ≤ ρ ^ (b - j) * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hρ.le _)
            exact pow_le_one₀ hρ.le hρ1
        _ = ρ ^ (b - j) := mul_one _
    have h2 : 1 / B ≤ ρ ^ (b - j) * Real.sqrt (N : ℝ) :=
      le_trans (le_trans hinvB hρpow) (le_mul_of_one_le_right (pow_nonneg hρ.le _) hsqrt1)
    calc |∑ α : ExpVec μ b, (∏ i, v i ^ α.toFun i) * jetFiberSum j α.toFun Fsum t₀|
        ≤ ∑ α : ExpVec μ b, (∏ i, |v i| ^ α.toFun i)
            * ((jetFiberCard μ j α.toFun : ℝ) * (d : ℝ) ^ j / B) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun α _ => ?_)
          rw [abs_mul, Finset.abs_prod]
          simp only [abs_pow]
          exact mul_le_mul_of_nonneg_left (hY j hj α) (Finset.prod_nonneg fun i _ => by positivity)
      _ = ((d : ℝ) ^ j / B) * (∑ i, |v i|) ^ j := by
          rw [show (∑ α : ExpVec μ b, (∏ i, |v i| ^ α.toFun i)
                * ((jetFiberCard μ j α.toFun : ℝ) * (d : ℝ) ^ j / B))
              = ((d : ℝ) ^ j / B) * ∑ α : ExpVec μ b, (∏ i, |v i| ^ α.toFun i)
                  * ((jetFiberCard μ j α.toFun : ℕ) : ℝ) from by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun α _ => by ring]
          rw [sum_fiberCard_weight hj (fun i => |v i|)]
      _ ≤ ((d : ℝ) ^ j / B) * ((μ : ℝ) * ‖v‖) ^ j := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => abs_nonneg _) hsum_le j
      _ ≤ ((μ : ℝ) ^ j * ρ ^ (b - j) * Real.sqrt (N : ℝ) * (d : ℝ) ^ j) * ‖v‖ ^ j := by
          rw [mul_pow]
          have hX3 : 0 ≤ (d : ℝ) ^ j * ((μ : ℝ) ^ j * ‖v‖ ^ j) := by positivity
          calc ((d : ℝ) ^ j / B) * ((μ : ℝ) ^ j * ‖v‖ ^ j)
              = (1 / B) * ((d : ℝ) ^ j * ((μ : ℝ) ^ j * ‖v‖ ^ j)) := by ring
            _ ≤ (ρ ^ (b - j) * Real.sqrt (N : ℝ)) * ((d : ℝ) ^ j * ((μ : ℝ) ^ j * ‖v‖ ^ j)) :=
                mul_le_mul_of_nonneg_right h2 hX3
            _ = ((μ : ℝ) ^ j * ρ ^ (b - j) * Real.sqrt (N : ℝ) * (d : ℝ) ^ j) * ‖v‖ ^ j := by
                ring

theorem siegel_poly_exists_v2 {μ b d : ℕ} (hb : 1 ≤ b) (hd : 1 ≤ d) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (Q : ℕ) (hQ : 1 ≤ Q)
    {ψ : (Fin μ → ℝ) → (Fin (μ + 1) → ℝ)}
    (hψ : ContDiffOn ℝ (b + 1 : ℕ) ψ (WilkiesDesign.openCube μ))
    (hψjet : ∀ k, k ≤ b → ∀ t ∈ WilkiesDesign.openCube μ,
      ‖iteratedFDeriv ℝ k ψ t‖ ≤ 1)
    (hψval : ∀ t ∈ WilkiesDesign.openCube μ, ∀ i, |ψ t i| ≤ 1)
    {t₀ : Fin μ → ℝ} (ht₀ : t₀ ∈ WilkiesDesign.openCube μ)
    (hcard : (Q + 1) ^ (Work.WilkiesH.monoCount (μ + 1) d)
        > (2 * (Work.WilkiesH.monoCount (μ + 1) d * Nat.ceil (ρ ^ (-(b : ℤ))) * Q) + 1)
            ^ (Work.WilkiesH.monoCount μ b)) :
    ∃ P : MvPolynomial (Fin (μ + 1)) ℤ, P ≠ 0 ∧ P.totalDegree ≤ d ∧
      (∀ m ∈ P.support, |(P.coeff m : ℤ)| ≤ (Q : ℤ)) ∧
      ∀ j, j ≤ b → ∀ v : Fin μ → ℝ,
        |iteratedFDeriv ℝ j (fun s => (P.map (Int.castRingHom ℝ)).eval (ψ s)) t₀
            (fun _ => v)|
          ≤ ((μ : ℝ) ^ j * ρ ^ (b - j)
              * Real.sqrt (Work.WilkiesH.monoCount (μ + 1) d : ℝ) * (d : ℝ) ^ j)
              * ‖v‖ ^ j :=
  siegel_poly_aux_v2 hb hd hρ hρ1 hQ hψ hψjet hψval ht₀ rfl rfl rfl rfl hcard

end Work.WilkiesH.Interp
