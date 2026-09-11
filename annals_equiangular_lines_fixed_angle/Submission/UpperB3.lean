import Submission.UpperB2
import Submission.EigenMult
import Submission.UpperB1
import Submission.UpperConfig
import Submission.ComponentsPF

open EquiangularLinesFixedAngle
open Matrix
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

noncomputable section

/-! # Case B2: complete bound (glue of UpperB2 + EigenMult)

Complete the case-B2 proof: given a *bounded-degree* equiangular configuration whose
associated graph has λ as an eigenvalue and spectral radius ρ0 > λ, show that with
`m :=` the multiplicity of λ (nullity of λI − A_G) one has `n ≤ d + 1 + m` and, for every
ε > 0, either `m` is below a constant `n₀` (component too small) or `m ≤ ε·n`.

Available machinery:
  * UpperB2 (all proven): `b2_countAbove_le_one`, `eigenvector_mem_spectrum`,
    `ofReal_le_spectralRadius_of_eigenvector`, `compRest_nonzero_of`,
    `exists_component_spectralRadius_eq`, `b2_other_components_rho_lt`,
    `b2_ker_restricts`, `b2_nullity_le_component`, `compExt_eigenvector`, `normSq_compExt`,
    `compExt_dot_compExt_of_ne`, `countAbove`.
  * UpperB1: `b1_rank_le_d_sub_one`, `spectrum_comp_subset`, `compRho_le`,
    `eigen_component_of`, `compRest_ker_comp`, `compReachable`, `compPreconnected`,
    `compVert` instances, `compCard` etc. (Components.lean).
  * EigenMult: `eigen_mult_eventual (Δ) : ∀ ε>0, ∃ n₀, ∀ V [Fintype V] [DecidableEq V]
    with n₀ ≤ card V, ∀ connected bounded-degree graph, ∀ λ>0 eigenvalue with an eigenvalue
    above it and at most one eigenvalue above λ : finrank(ker(λI−A)) ≤ ε·card V`.
  * UpperConfig: `graphMatrix_decomp`, `graphMatrix_posSemidef_of_config`,
    `rank_graphMatrix_le`, `rank_sub_le` (Upper0), `rank_add_nullity_eq` (UpperCase),
    `half_ones_posSemidef`, `onesMatrix_posSemidef`, `dotProduct_ones`.
  * MatrixFacts/Perron/PfExtra/GraphSpec: Fin-version PF facts (`nonneg_eigenvector_of_spectralRadius`,
    `exists_eigenvalue_eq_of_spectralRadius`, `adjMatrix_isHermitian`, `adjMatrix_nonneg`,
    `eigenvalues_le_of_spectralRadius`, `sub_psd_of_spectralRadius`, `sub_psd_of_eigenvalues_le`,
    `spectralRadius_ge_eigenvalue`).

PROVE ALL DECLARATIONS below with complete proofs, no placeholders.  Suggested flow for `b2_bound`:
 1. `hA := adjMatrix_isHermitian_any G`? (any Hermitian proof; use `G.adjMatrix ℝ` Hermitian
    proof consistently).  From the eigenvector hypothesis `∃x≠0, A*x = λx` and the ρ0-form,
    obtain the top component `c0` with ρ(compAdj G c0) = ofReal ρ0 via
    `exists_component_spectralRadius_eq` (applied to an eigenvector of value ρ0 coming from
    `exists_eigenvalue_eq_of_spectralRadius_any` on A with the ρ0-form).
 2. All other components have ρ < ofReal λ (`b2_other_components_rho_lt`).
 3. The nullity `m := finrank(ker((λI−A).mulVecLin))` satisfies
    `n = rank(λI−A) + m` (rank_add_nullity_eq), `rank(λI−A) ≤ d + 1` (rank_sub_le:
    λI−A = graphMatrix − ½J and rank graphMatrix ≤ d), and `m ≤ finrank(ker(λI−A_{c0}))`
    (`b2_nullity_le_component`); hence `n ≤ d + 1 + m` with `m0 := finrank(ker((λI−A_{c0}).mulVecLin))`.
 4. Bound m0 via `eigen_mult_eventual Δ` with the SAME ε: it yields n₀.  If card c0 < n₀ then
    m0 ≤ card c0 ≤ n₀ (and m ≤ m0).  Otherwise card c0 ≥ n₀ and the component graph
    (cGraph G c0, vertex type c0) satisfies the eigen-mult hypotheses: connected
    (`compReachable` / `compPreconnected`), degree ≤ Δ (degrees in induced ≤ in G: prove
    lemma `component_degree_le`), eigenvalue λ>0 of compAdj G c0 (from the λ-eigenvector x of
    A: all components but c0 have ρ<λ so their restrictions vanish; restriction to c0 is a
    λ-eigenvector — prove a lemma `component_eigenvalue_of_eigenvalue`), an eigenvalue strictly
    above λ (ρ0, via PF eigenvector of compAdj G c0), and at most one eigenvalue above λ
    (`countAbove (compAdj G c0) hAc (lam α) ≤ 1`: prove a lemma `countAbove_component_le_one`
    from `b2_countAbove_le_one` + `countAbove_le_of_comp` which shows countAbove of a
    component is at most that of the whole graph by embedding eigenvalues).
    Then eigen_mult_eventual gives m0 ≤ ε·card c0 ≤ ε·n.
 5. Output `∃ m : ℕ, n ≤ d + 1 + m ∧ (m ≤ n₀ ∨ (m : ℝ) ≤ ε * (n : ℝ))` with m := nullity
    (and also expose the bound m0 ≤ ... for the second alternative).

Good luck!
-/

/-- the degree of a vertex inside its component is at most its degree in the graph. -/
lemma component_degree_le {n : ℕ} (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent)
    (v : c) : (cGraph G c).degree v ≤ G.degree v.1 := by
  classical
  let S : Finset c := (cGraph G c).neighborFinset v
  let T : Finset (Fin n) := G.neighborFinset v.1
  have hST : S.image (fun w : c => (w : Fin n)) ⊆ T := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨w, hw, rfl⟩
    have hadj : (cGraph G c).Adj v w :=
      (SimpleGraph.mem_neighborFinset (cGraph G c) v w).mp (by simpa [S] using hw)
    rw [SimpleGraph.mem_neighborFinset]
    exact (cGraph_adj_iff G c).mp hadj
  have hcard1 : S.card = (S.image (fun w : c => (w : Fin n))).card := by
    symm
    apply Finset.card_image_of_injective
    intro a b hab
    exact Subtype.ext hab
  calc
    (cGraph G c).degree v = S.card := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
    _ = (S.image (fun w : c => (w : Fin n))).card := hcard1
    _ ≤ T.card := Finset.card_le_card hST
    _ = G.degree v.1 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]

/-- extension of two functions on a component preserves their dot product. -/
lemma compExt_dot {n : ℕ} (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent)
    (u v : c → ℝ) :
    (compExt G c u) ⬝ᵥ (compExt G c v) = u ⬝ᵥ v := by
  classical
  calc
    (compExt G c u) ⬝ᵥ (compExt G c v) = ∑ k : Fin n, (compExt G c u k) * (compExt G c v k) := by
      simp [dotProduct]
    _ = ∑ k : Fin n, compExt G c (fun i : c => u i * v i) k := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h : k ∈ c.supp
      · simp [compExt_apply_mem G c u h, compExt_apply_mem G c v h,
          compExt_apply_mem G c (fun i : c => u i * v i) h]
      · simp [compExt_apply_not_mem G c u h, compExt_apply_not_mem G c v h,
          compExt_apply_not_mem G c (fun i : c => u i * v i) h]
    _ = ∑ i : c, u i * v i := by
      exact sum_compExt G c (fun i : c => u i * v i)
    _ = u ⬝ᵥ v := by
      simp [dotProduct]

/-- two orthonormal eigenvectors of `A_G` with eigenvalues strictly above `lam α`
contradict `M ⪰ 0`. -/
lemma two_eigen_above_contra {α : ℝ} {n : ℕ} (G : SimpleGraph (Fin n))
    (hMpsd : (graphMatrix α G).PosSemidef)
    {v w : Fin n → ℝ} (hvw : v ⬝ᵥ w = 0) (hvv : v ⬝ᵥ v = 1) (hww : w ⬝ᵥ w = 1)
    {μv μw : ℝ} (hvμ : lam α < μv) (hwμ : lam α < μw)
    (hv : (G.adjMatrix ℝ) *ᵥ v = μv • v) (hw : (G.adjMatrix ℝ) *ᵥ w = μw • w) :
    False := by
  classical
  have hcontra : ∀ (p q : ℝ), (p ≠ 0 ∨ q ≠ 0) →
      (∑ k : Fin n, (p • v + q • w) k) = 0 → False := by
    intro p q hpq hsum
    let z : Fin n → ℝ := p • v + q • w
    have hnorm : z ⬝ᵥ z = p ^ 2 + q ^ 2 := by
      dsimp [z]
      have h := normSq_two v w hvw p q
      rw [hvv, hww] at h
      ring_nf at h ⊢
      exact h
    have hquad : z ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ z) = p ^ 2 * μv + q ^ 2 * μw := by
      dsimp [z]
      have h := quad_two (G.adjMatrix ℝ) v w μv μw hv hw hvw p q
      rw [hvv, hww] at h
      ring_nf at h ⊢
      exact h
    have hsum0 : (∑ k : Fin n, z k) = 0 := by
      simpa [z] using hsum
    have hzle : z ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ z) ≤ (lam α) * (z ⬝ᵥ z) := by
      have hq0 := graphMatrix_quad_nonneg G hMpsd z
      have hq := graphMatrix_quad (α := α) G z
      rw [hq] at hq0
      rw [hsum0] at hq0
      norm_num at hq0
      linarith
    have hgt : (lam α) * (z ⬝ᵥ z) < z ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ z) := by
      rw [hnorm, hquad]
      have hma : 0 < μv - lam α := by linarith
      have hmb : 0 < μw - lam α := by linarith
      have hmain : 0 < p ^ 2 * (μv - lam α) + q ^ 2 * (μw - lam α) := by
        rcases hpq with hpn | hqn
        · have h1 : 0 < p ^ 2 * (μv - lam α) := mul_pos (sq_pos_of_ne_zero hpn) hma
          have h2 : 0 ≤ q ^ 2 * (μw - lam α) := mul_nonneg (sq_nonneg q) (le_of_lt hmb)
          nlinarith
        · have h1 : 0 ≤ p ^ 2 * (μv - lam α) := mul_nonneg (sq_nonneg p) (le_of_lt hma)
          have h2 : 0 < q ^ 2 * (μw - lam α) := mul_pos (sq_pos_of_ne_zero hqn) hmb
          nlinarith
      nlinarith
    linarith
  by_cases hv0 : (∑ k : Fin n, v k) = 0
  · have hsum : (∑ k : Fin n, ((1 : ℝ) • v + (0 : ℝ) • w) k) = 0 := by
      simpa [hv0]
    exact hcontra 1 0 (Or.inl (by norm_num)) hsum
  · have hsum : (∑ k : Fin n, ((∑ t : Fin n, w t) • v + (-(∑ t : Fin n, v t)) • w) k) = 0 := by
      calc
        (∑ k : Fin n, ((∑ t : Fin n, w t) • v + (-(∑ t : Fin n, v t)) • w) k)
            = (∑ t : Fin n, w t) * (∑ k : Fin n, v k) + (-(∑ t : Fin n, v t)) * (∑ k : Fin n, w k) := by
                simpa using (sum_add_smul (ι := Fin n) (∑ t : Fin n, w t) (-(∑ t : Fin n, v t)) v w)
        _ = 0 := by ring
    exact hcontra (∑ t : Fin n, w t) (-(∑ t : Fin n, v t)) (Or.inr (neg_ne_zero.mpr hv0)) hsum

/-- eigenvalue values of a component among those of the whole graph, at most one above λ
in case B2. -/
lemma countAbove_component_le_one {α : ℝ} {n : ℕ} (G : SimpleGraph (Fin n))
    (hα0 : 0 < α) (hα1 : α < 1) (hMpsd : (graphMatrix α G).PosSemidef)
    (c : G.ConnectedComponent) :
    countAbove (compAdj G c) (compAdj_isHermitian G c) (lam α) ≤ 1 := by
  classical
  by_contra hnot
  have hnot' : ¬ Fintype.card {i : c // (lam α) < (compAdj_isHermitian G c).eigenvalues i} ≤ 1 := by
    change ¬ countAbove (compAdj G c) (compAdj_isHermitian G c) (lam α) ≤ 1
    exact hnot
  have hge : 2 ≤ Fintype.card {i : c // (lam α) < (compAdj_isHermitian G c).eigenvalues i} := by omega
  have hone : 1 < Fintype.card {i : c // (lam α) < (compAdj_isHermitian G c).eigenvalues i} := by omega
  rcases Fintype.exists_pair_of_one_lt_card (α := {i : c // (lam α) < (compAdj_isHermitian G c).eigenvalues i}) hone with ⟨a, b, hab⟩
  let i : c := a.1
  let j : c := b.1
  have hij : i ≠ j := by
    intro heq
    apply hab
    apply Subtype.ext
    simpa [i, j] using heq
  have hi : (lam α) < (compAdj_isHermitian G c).eigenvalues i := by
    simpa [i] using a.2
  have hj : (lam α) < (compAdj_isHermitian G c).eigenvalues j := by
    simpa [j] using b.2
  let vc : c → ℝ := ((compAdj_isHermitian G c).eigenvectorBasis i).ofLp
  let wc : c → ℝ := ((compAdj_isHermitian G c).eigenvectorBasis j).ofLp
  let v : Fin n → ℝ := compExt G c vc
  let w : Fin n → ℝ := compExt G c wc
  have hvcwc : vc ⬝ᵥ wc = 0 := by
    dsimp [vc, wc]
    exact eigenvector_dotProduct_other (A := compAdj G c) (hA := compAdj_isHermitian G c) hij
  have hvvc : vc ⬝ᵥ vc = 1 := by
    dsimp [vc]
    exact eigenvector_dotProduct_self_any (compAdj G c) (compAdj_isHermitian G c) i
  have hwwc : wc ⬝ᵥ wc = 1 := by
    dsimp [wc]
    exact eigenvector_dotProduct_self_any (compAdj G c) (compAdj_isHermitian G c) j
  have hvw : v ⬝ᵥ w = 0 := by
    dsimp [v, w]
    rw [compExt_dot]
    exact hvcwc
  have hvv : v ⬝ᵥ v = 1 := by
    dsimp [v]
    rw [compExt_dot]
    exact hvvc
  have hww : w ⬝ᵥ w = 1 := by
    dsimp [w]
    rw [compExt_dot]
    exact hwwc
  have hAcv : (compAdj G c) *ᵥ vc = ((compAdj_isHermitian G c).eigenvalues i) • vc := by
    dsimp [vc]
    exact (compAdj_isHermitian G c).mulVec_eigenvectorBasis i
  have hAcw : (compAdj G c) *ᵥ wc = ((compAdj_isHermitian G c).eigenvalues j) • wc := by
    dsimp [wc]
    exact (compAdj_isHermitian G c).mulVec_eigenvectorBasis j
  have hAv : (G.adjMatrix ℝ) *ᵥ v = ((compAdj_isHermitian G c).eigenvalues i) • v := by
    dsimp [v]
    exact compExt_eigenvector G c (u := vc) hAcv
  have hAw : (G.adjMatrix ℝ) *ᵥ w = ((compAdj_isHermitian G c).eigenvalues j) • w := by
    dsimp [w]
    exact compExt_eigenvector G c (u := wc) hAcw
  exact two_eigen_above_contra G hMpsd hvw hvv hww hi hj hAv hAw

/-- If λ is an eigenvalue of `A_G` and all other components have spectral radius `< ofReal λ`,
then λ is an eigenvalue of `compAdj G c0` whenever it is an eigenvalue of `A_G`. -/
lemma component_eigenvalue_of_eigenvalue {α : ℝ} {n : ℕ} (G : SimpleGraph (Fin n))
    (hα0 : 0 < α) (hα1 : α < 1)
    (hMpsd : (graphMatrix α G).PosSemidef)
    {ρ0 : ℝ} (hlr : lam α < ρ0)
    (c0 : G.ConnectedComponent)
    (hc0 : spectralRadius ℝ (compAdj G c0) = ENNReal.ofReal ρ0)
    (hlam0 : ∃ x : Fin n → ℝ, x ≠ 0 ∧ (G.adjMatrix ℝ) *ᵥ x = lam α • x) :
    ∃ y : c0 → ℝ, y ≠ 0 ∧ (compAdj G c0) *ᵥ y = lam α • y := by
  classical
  rcases hlam0 with ⟨x, hx0, hAx⟩
  have hker : ((lam α • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ) *ᵥ x) = 0 := by
    rw [mulVec_sub_any]
    have hsc : ((lam α • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x) = lam α • x := by
      ext i
      simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.one_apply, Finset.sum_ite_eq]
    rw [hsc, hAx]
    simp
  have hxres : compRest G c0 x ≠ 0 := by
    intro hres0
    have hx_all_zero : x = 0 := by
      funext v0
      by_contra hxv0
      let c := G.connectedComponentMk v0
      have hv0 : v0 ∈ c.supp := by
        simp [c, SimpleGraph.ConnectedComponent.mem_supp_iff]
      have hcne : c ≠ c0 := by
        intro hceq
        have hval := congrFun hres0 ⟨v0, (by rw [hceq] at hv0; exact hv0)⟩
        have hz : x v0 = 0 := by simpa [compRest] using hval
        exact hxv0 hz
      have hlt : spectralRadius ℝ (compAdj G c) < ENNReal.ofReal (lam α) :=
        b2_other_components_rho_lt G hα0 hα1 hMpsd hlr c0 hc0 c hcne
      have hxres_c : compRest G c x ≠ 0 := by
        intro hz
        have hval := congrFun hz ⟨v0, hv0⟩
        simpa [compRest] using hxv0 hval
      exact (not_lt_of_ge (compRest_nonzero_of G c x hker hxres_c)) hlt
    exact hx0 hx_all_zero
  refine ⟨compRest G c0 x, hxres, ?_⟩
  have hkc := compRest_ker_comp G c0 (lam0 := lam α) (x := x) hker
  have hlin : (lam α) • compRest G c0 x - (compAdj G c0) *ᵥ compRest G c0 x = 0 := by
    simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using hkc
  exact (sub_eq_zero.mp hlin).symm

theorem b2_bound {α : ℝ} {Δ : ℕ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ ε : ℝ, 0 < ε →
    ∃ n₀ : ℕ, ∀ {n d : ℕ} (v : Fin n → Euc d) (hn : 0 < n),
      (∀ i, ‖v i‖ = 1) →
      (∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α) →
      (∀ i : Fin n, (assocGraph α v).degree i ≤ Δ) →
      (∃ x : Fin n → ℝ, x ≠ 0 ∧ (assocGraph α v).adjMatrix ℝ *ᵥ x = (lam α) • x) →
      (∃ ρ0 : ℝ, lam α < ρ0 ∧
         spectralRadius ℝ ((assocGraph α v).adjMatrix ℝ) = ENNReal.ofReal ρ0) →
      ∃ m : ℕ, n ≤ d + 1 + m ∧ (m ≤ n₀ ∨ (m : ℝ) ≤ ε * (n : ℝ)) := by
  classical
  intro ε hε
  rcases eigen_mult_eventual Δ ε hε with ⟨n0, hn0⟩
  refine ⟨n0, ?_⟩
  intro n d v hn hvnorm hvangle hdeg hx hρhyp
  let G : SimpleGraph (Fin n) := assocGraph α v
  have hlam0 : 0 < lam α := lam_pos hα0 hα1
  have hMpsd : (graphMatrix α G).PosSemidef := by
    dsimp [G]
    exact graphMatrix_posSemidef_of_config v hα0 hvnorm hvangle
  rcases hρhyp with ⟨ρ0, hlr, hρG⟩
  have hρ0pos : 0 < ρ0 := lt_trans hlam0 hlr
  have hcardn : 0 < Fintype.card (Fin n) := by simpa using hn
  rcases nonneg_eigenvector_of_spectralRadius_any hcardn (G.adjMatrix ℝ) (adjMatrix_isHermitian G)
    (adjMatrix_nonneg G) hρ0pos (by simpa [G] using hρG) with ⟨u0, hu0nn, hu0sum, hu0eig⟩
  have hu0ne : u0 ≠ 0 := by
    intro hu0z
    have hz : (∑ i : Fin n, u0 i) = 0 := by simp [hu0z]
    linarith
  rcases exists_component_spectralRadius_eq G hρ0pos (by simpa [G] using hρG) u0 hu0ne hu0eig with ⟨c0, hc0⟩
  let B : Matrix (Fin n) (Fin n) ℝ := (lam α) • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ
  let m : ℕ := Module.finrank ℝ (LinearMap.ker B.mulVecLin)
  let B0 : Matrix c0 c0 ℝ := (lam α) • (1 : Matrix c0 c0 ℝ) - compAdj G c0
  let m0 : ℕ := Module.finrank ℝ (LinearMap.ker B0.mulVecLin)
  -- n = rank B + m, rank B ≤ d + 1
  have hrank_add : B.rank + m = n := by
    dsimp [m, B]
    exact rank_add_nullity_eq n ((lam α) • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ)
  have hD : B = graphMatrix α G - (1 / 2 : ℝ) • onesMatrix n := by
    dsimp [B]
    exact lam_sub_adj_eq_graph_sub (α := α) (G := G)
  have hrank : B.rank ≤ d + 1 := by
    have hle1 := rank_sub_le (graphMatrix α G) (((1 / 2 : ℝ) • onesMatrix n))
    have hM : (graphMatrix α G).rank ≤ d := by
      dsimp [G]
      exact rank_graphMatrix_le v hα0 hvnorm hvangle
    have hJ : (((1 / 2 : ℝ) • onesMatrix n).rank) ≤ 1 := rank_half_ones_le n
    have h1 : (graphMatrix α G - (1 / 2 : ℝ) • onesMatrix n).rank ≤ d + 1 := by
      have hsum : (graphMatrix α G).rank + (((1 / 2 : ℝ) • onesMatrix n).rank) ≤ d + 1 := by omega
      exact le_trans hle1 hsum
    rwa [← hD] at h1
  have hnbd : n ≤ d + 1 + m := by omega
  -- multiplicity bounds
  have hmm0 : m ≤ m0 := by
    dsimp [m, m0, B, B0]
    exact b2_nullity_le_component G hα0 hα1 hMpsd hlr c0 hc0
  have hm0card : m0 ≤ Fintype.card c0 := by
    dsimp [m0, B0]
    have hle := Submodule.finrank_le (LinearMap.ker (((lam α) • (1 : Matrix c0 c0 ℝ) - compAdj G c0).mulVecLin))
    have hpi : Module.finrank ℝ (c0 → ℝ) = Fintype.card c0 := Module.finrank_pi ℝ
    exact le_trans hle (le_of_eq hpi)
  have hcardc0 : Fintype.card c0 ≤ n := by
    have hinj : Function.Injective (fun v : c0 => (v : Fin n)) := by
      intro a b hab
      exact Subtype.ext hab
    simpa using (Fintype.card_le_of_injective (fun v : c0 => (v : Fin n)) hinj)
  -- case split on component size
  by_cases hsmall : Fintype.card c0 < n0
  · refine ⟨m, hnbd, ?_⟩
    left
    omega
  · refine ⟨m, hnbd, ?_⟩
    right
    have hlarge : n0 ≤ Fintype.card c0 := le_of_not_gt hsmall
    have hconn : ∀ i j : c0, (cGraph G c0).Reachable i j := fun i j => compReachable G c0 i j
    have hdegcomp : ∀ v : c0, (cGraph G c0).degree v ≤ Δ := by
      intro v
      exact le_trans (component_degree_le G c0 v) (hdeg v.1)
    rcases hx with ⟨x, hx0, hAx⟩
    have hceig := component_eigenvalue_of_eigenvalue G hα0 hα1 hMpsd hlr c0 hc0 ⟨x, hx0, hAx⟩
    have hcardc0pos : 0 < Fintype.card c0 := compCard_pos G c0
    rcases nonneg_eigenvector_of_spectralRadius_any hcardc0pos (compAdj G c0)
      (compAdj_isHermitian G c0) (compAdj_nonneg G c0) hρ0pos hc0 with ⟨yc, hycnn, hycsum, hyceig⟩
    have hycne : yc ≠ 0 := by
      intro hycz
      have hz : (∑ i : c0, yc i) = 0 := by simp [hycz]
      linarith
    have habove : ∃ mu : ℝ, lam α < mu ∧ ∃ y : c0 → ℝ, y ≠ 0 ∧ compAdj G c0 *ᵥ y = mu • y :=
      ⟨ρ0, hlr, ⟨yc, hycne, hyceig⟩⟩
    have hcnt : Fintype.card {i : c0 // lam α < (compAdj_isHermitian G c0).eigenvalues i} ≤ 1 := by
      exact countAbove_component_le_one G hα0 hα1 hMpsd c0
    have hres := hn0 c0 hlarge (cGraph G c0) (compAdj_isHermitian G c0) hconn hdegcomp hlam0
      hceig habove hcnt
    have hm0e : (m0 : ℝ) ≤ ε * (Fintype.card c0 : ℝ) := by
      dsimp [m0, B0]
      exact hres
    have hmm0r : (m : ℝ) ≤ (m0 : ℝ) := by exact_mod_cast hmm0
    have hcc : (Fintype.card c0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcardc0
    have hεc : ε * (Fintype.card c0 : ℝ) ≤ ε * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hcc (le_of_lt hε)
    exact le_trans hmm0r (le_trans hm0e hεc)


end
end Submission
