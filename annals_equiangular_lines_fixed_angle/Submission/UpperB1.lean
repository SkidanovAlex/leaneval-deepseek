import Submission.UpperCase
import Submission.ComponentsPF
import Submission.UpperRelabel
import Submission.KOrder
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Adjugate

open EquiangularLinesFixedAngle
open Matrix
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

noncomputable section

/-- canonical (classical) decidability of equality on a component type: definitionally the
same as the `DecidableEq` instance that generic lemmas bake for arbitrary index types, so
component statements and generic matrix lemmas see the same instances. -/
instance (priority := 1000) compDecEq {n : ℕ} (G : SimpleGraph (Fin n))
    (c : G.ConnectedComponent) : DecidableEq c :=
  fun a b => Classical.propDecidable (a = b)

/-! # Case B1: graph with spectral radius exactly λ

Complete the proof of the case-B1 upper bound: for an equiangular family
`v : Fin n → Euc d` (unit vectors, pairwise `|⟪v i, v j⟫| = α`) whose associated graph
`G := assocGraph α v` has `ρ(G) = λ` (λ := lam α > 0), one has
`n ≤ k₀(d−1)/(k₀−1)` where `k₀ := (spectralRadiusOrder λ).toNat` (assumed finite).

The three ingredients (all to be proved in this file; import `Submission.UpperCase` for
`b1_rank_le_d_sub_one`):
  (1) rank(λI − A_G) ≤ d − 1                     -- DONE (b1_rank_le_d_sub_one)
  (2) nullity(λI − A_G) ≤ |J|,  J := {components c with ρ(A_c) = λ}
  (3) n ≥ k₀·|J|   (each ρ=λ component has ≥ k₀ vertices)

then the plain arithmetic n ≤ (d−1) + (d−1)/(k₀−1) = k₀(d−1)/(k₀−1).

NOTATION (from Submission.Components): for `G : SimpleGraph (Fin n)` and a component
`c : G.ConnectedComponent`, the component type is `c` (a subtype of `Fin n`), the induced
graph is `cGraph G c : SimpleGraph c`, its adjacency matrix `compAdj G c : Matrix c c ℝ`,
the component size is `compCard G c := Fintype.card c`.  Facts available:
  * `compPreconnected G c` : (cGraph G c).Preconnected
  * `compRest_ker G c x hx` : x ∈ ker(λI−A_G) → (restriction to c) ∈ ker(λI − A_c)
  * `lamI_sub_adj_restrict`, `compRest`, `compExt`
  * generic PF (Submission.ComponentsPF): `nonneg_eigenvector_of_spectralRadius_any`,
    `positive_eigenvector_of_connected_any`, `eigenspace_eq_span_of_positive_any`,
    `spectralRadius_ge_eigenvalue_any`, `eigenvalues_le_of_spectralRadius_any`,
    `exists_eigenvalue_of_mem_spectrum_any`, `mem_spectrum_iff_eigenvalue_any`
    (all with index type `ι : Type*` with `[Fintype ι]`, `[DecidableEq ι]` where noted)
  * `Submission.b1_rank_le_d_sub_one` (UpperCase.lean)
  * `Submission.spectralRadiusOrder_toNat_le_card` (UpperRelabel.lean)
  * `rank_add_nullity_eq n B` (UpperCase.lean): B.rank + finrank(ker B.mulVecLin) = n

GUIDE:
1. `eigen_component_of`: an eigenvalue μ of `compAdj G c` is an eigenvalue of `G.adjMatrix ℝ`
   (embed the eigenvector by zero outside c; use Components' adj_restrict_mem / adj_compExt_outside).
2. `spectrum_comp_subset`: spectrum (compAdj G c) ⊆ spectrum (G.adjMatrix ℝ)
   (members in spectrum of A_c are eigenvalues of A_c by `exists_eigenvalue_of_mem_spectrum_any`;
   they come with eigenvectors; apply `eigen_component_of`; then convert eigenvector-with-value
   of a Hermitian matrix to membership in its spectrum, e.g. via the pattern in
   Upper0.lean `mem_spectrum_iff_eigenvalue`: charpoly = ∏ (X − C eigenvalues), and an eigenvector
   with value ν forces charpoly.IsRoot ν (use `Matrix.eval_charpoly` and show the matrix
   `ν•1 − A` has a nontrivial kernel so its det is 0).)
3. `spectralRadius_le_of_spectrum_subset` and `compRho_le` (component spectral radius ≤ graph
   spectral radius).
4. For the nullity bound `nullity_le_card`:
   - B := (λ•1 − A_G); nullity := n − B.rank = finrank(ker B.mulVecLin) (via rank_add_nullity_eq).
   - Build a linear injection from `ker B.mulVecLin` into the direct product
     `{c // ρ(A_c) = λ} → ℝ` by mapping x to (for each λ-component c) the scalar t_c with
     `compRest G c x = t_c • u_c`, where `u_c` is the PF eigenvector of component c
     (nonneg_eigenvector_of_spectralRadius_any applied to compAdj G c; positive by
     positive_eigenvector_of_connected_any since the component graph is connected).
     Show that for x ∈ ker: on a λ-component, x|_c = t_c·u_c (eigenspace_eq_span_of_positive_any),
     and on a non-λ component, x|_c = 0 (because λ-eigenvalue would force ofReal λ ≤ ρ(A_c)
     by spectralRadius_ge_eigenvalue_any, contradicting ρ(A_c) < ofReal λ; the case ρ(A_c) >
     ofReal λ cannot occur since compRho_le gives ρ(A_c) ≤ ρ(G) = ofReal λ).
   - Conclude dim ker ≤ card J by finrank of the target (Module.finrank_pi / card of function
     space = card) or by showing the map to `J → ℝ` is injective and using an injective-linear-map
     finrank bound.
5. `card_bound`: each λ-component c satisfies compCard G c ≥ k₀.  Use
   `spectralRadiusOrder_toNat_le_card (cGraph G c)` with Fintype.card c = compCard.
   Then the total number n of vertices is ≥ sum over J of compCard ≥ k₀·|J|: build the injection
   from the disjoint union (Σ c : J, c) into Fin n by projecting to the underlying vertex
   (`Fintype.card_sigma` = sum of cards ≤ n by injectivity).
6. `b1_bound`: assemble. Let k₀ := (spectralRadiusOrder λ).toNat.
   nullity + rank = n; rank ≤ d−1 (b1_rank_le_d_sub_one); nullity ≤ |J|; (k₀−1)·|J| ≤ rank??
   -- NOTE: use instead: rank = n − nullity ≥ n − |J| ≥ k₀|J| − |J| = (k₀−1)|J|, i.e.
   |J|·(k₀−1) ≤ rank, and rank ≤ d−1, so n = rank + nullity ≤ (d−1) + |J| ≤ (d−1) + (d−1)/(k₀−1).
   Do the arithmetic in ℝ (casts of the natural numbers), concluding
   `(n : ℝ) ≤ ((k₀ * (d-1) : ℕ) : ℝ) / ((k₀ - 1 : ℕ) : ℝ)`.
   You may need `spectralRadiusOrder_toNat_ge_two` (Perron.lean) for k₀ ≥ 2 (positivity of
   the denominator).
   For simplicity prove the intermediate real inequality in the form
   (n : ℝ) ≤ (d - 1 : ℝ) + (d - 1 : ℝ) / ((k₀ - 1 : ℕ) : ℝ) and then nlinarith/ring it into the
   target fraction (k₀ ≥ 2 so the denominator is positive and k₀/(k₀−1) = 1 + 1/(k₀−1)).

PROVE ALL lemmas with no placeholders.  Read UpperCase.lean/UpperRelabel.lean/ComponentsPF.lean for the
established style.  You may add helpers.  Keep the statements below EXACTLY.  Good luck!
-/

/-- an eigenvector with real eigenvalue value makes that value lie in the real spectrum. -/
lemma eigen_mem_spectrum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) {μ : ℝ} {x : ι → ℝ} (hx : x ≠ 0)
    (hAx : A *ᵥ x = μ • x) : μ ∈ spectrum ℝ A := by
  classical
  let B : Matrix ι ι ℝ := μ • (1 : Matrix ι ι ℝ) - A
  have hBx : B *ᵥ x = 0 := by
    dsimp [B]
    rw [Matrix.sub_mulVec]
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, hAx]
    simp
  have hex : ∃ i : ι, x i ≠ 0 := by
    by_contra hnot
    apply hx
    funext i
    by_contra hne
    exact hnot ⟨i, hne⟩
  rcases hex with ⟨i, hi⟩
  have hdet : B.det = 0 := by
    exact det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors (M := B) (v := x) hBx
      (i := i) (mem_nonZeroDivisors_iff_ne_zero.mpr hi)
  have hscalar : Matrix.scalar ι μ = μ • (1 : Matrix ι ι ℝ) := by
    ext a b
    by_cases h : a = b <;> simp [Matrix.scalar, h]
  have hEv : A.charpoly.eval μ = 0 := by
    rw [Matrix.eval_charpoly]
    calc
      (Matrix.scalar ι μ - A).det = B.det := by rw [hscalar]
      _ = 0 := hdet
  exact Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hEv

/-- an eigenvector with real eigenvalue value makes that value one of the Hermitian
eigenvalues (needs the matrix to be Hermitian). -/
lemma eigenvalue_of_eigenvector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) {μ : ℝ} {x : ι → ℝ}
    (hx : x ≠ 0) (hAx : A *ᵥ x = μ • x) : ∃ j : ι, hA.eigenvalues j = μ := by
  classical
  exact exists_eigenvalue_of_mem_spectrum_any A hA (eigen_mem_spectrum A hx hAx)

/-- the adjacency matrix of a component is Hermitian. -/
lemma compAdj_isHermitian {n : ℕ} (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) :
    (compAdj G c).IsHermitian := by
  classical
  dsimp [compAdj]
  rw [Matrix.isHermitian_iff_isSymm]
  exact SimpleGraph.isSymm_adjMatrix (cGraph G c)

/-- entries of a component adjacency matrix are nonnegative. -/
lemma compAdj_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent)
    (i j : c) : 0 ≤ (compAdj G c) i j := by
  classical
  by_cases h : (cGraph G c).Adj i j <;> simp [compAdj, SimpleGraph.adjMatrix_apply, h]

/-- every component of a graph is nonempty. -/
lemma compCard_pos {n : ℕ} (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) :
    0 < Fintype.card c := by
  classical
  rcases (SimpleGraph.ConnectedComponent.nonempty_supp c) with ⟨v, hv⟩
  exact Fintype.card_pos_iff.mpr ⟨⟨v, hv⟩⟩

/-- an eigenvalue of a component adjacency is an eigenvalue of the whole adjacency. -/
lemma eigen_component_of {n : ℕ} (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent)
    {μ : ℝ} {y : c → ℝ} (hy : y ≠ 0)
    (hAy : (compAdj G c) *ᵥ y = μ • y) :
    ∃ x : Fin n → ℝ, x ≠ 0 ∧ (G.adjMatrix ℝ) *ᵥ x = μ • x := by
  classical
  refine ⟨compExt G c y, ?_, ?_⟩
  · intro hx0
    apply hy
    funext v
    have h := congrFun hx0 v.1
    rw [compExt_apply_mem G c y v.2] at h
    exact h
  · funext w
    by_cases hw : w ∈ c.supp
    · have hres : compRest G c (compExt G c y) = y := by
        funext v
        simp [compRest, compExt_apply_mem G c y v.2]
      have hadj := adj_restrict_mem G c (compExt G c y) ⟨w, hw⟩
      calc
        ((G.adjMatrix ℝ) *ᵥ compExt G c y) w
            = ((cGraph G c).adjMatrix ℝ *ᵥ compRest G c (compExt G c y)) ⟨w, hw⟩ := hadj
        _ = ((cGraph G c).adjMatrix ℝ *ᵥ y) ⟨w, hw⟩ := by rw [hres]
        _ = (μ • y) ⟨w, hw⟩ := by
              have h := congrFun hAy ⟨w, hw⟩
              simpa [compAdj] using h
        _ = (μ • compExt G c y) w := by
              simp [compExt_apply_mem G c y hw, Pi.smul_apply]
    · have hz : ((G.adjMatrix ℝ) *ᵥ compExt G c y) w = 0 := adj_compExt_outside G c y hw
      rw [hz]
      simp [compExt_apply_not_mem G c y hw, Pi.smul_apply]

/-- eigenvalues of a component lie among the eigenvalues of the whole graph (spectrum inclusion). -/
lemma spectrum_comp_subset {n : ℕ} (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) :
    spectrum ℝ (compAdj G c) ⊆ spectrum ℝ (G.adjMatrix ℝ) := by
  classical
  intro μ hμ
  have hAc : (compAdj G c).IsHermitian := compAdj_isHermitian G c
  rcases exists_eigenvalue_of_mem_spectrum_any (compAdj G c) hAc hμ with ⟨j, hj⟩
  let y : c → ℝ := (hAc.eigenvectorBasis j).ofLp
  have hy0 : y ≠ 0 := by
    intro hy0'
    have hd := eigenvector_dotProduct_self_any (compAdj G c) hAc j
    change y ⬝ᵥ y = 1 at hd
    rw [hy0'] at hd
    simp at hd
  have hAy : (compAdj G c) *ᵥ y = μ • y := by
    have h1 := Matrix.IsHermitian.mulVec_eigenvectorBasis hAc j
    dsimp [y]
    rw [h1, hj]
  rcases eigen_component_of G c hy0 hAy with ⟨x, hx0, hAx⟩
  exact eigen_mem_spectrum (G.adjMatrix ℝ) hx0 hAx

/-- spectral radius monotone in the spectrum. -/
lemma spectralRadius_le_of_spectrum_subset {ι ι' : Type*} [Fintype ι] [Fintype ι']
    {A : Matrix ι ι ℝ} {B : Matrix ι' ι' ℝ} (h : spectrum ℝ A ⊆ spectrum ℝ B) :
    spectralRadius ℝ A ≤ spectralRadius ℝ B := by
  classical
  unfold spectralRadius
  apply iSup_le
  intro μ
  apply iSup_le
  intro hμ
  have hμ' : μ ∈ spectrum ℝ B := h hμ
  exact le_trans
    (le_iSup (fun _ : μ ∈ spectrum ℝ B => ((‖μ‖₊ : NNReal) : ENNReal)) hμ')
    (le_iSup (fun k : ℝ => ⨆ _ : k ∈ spectrum ℝ B, ((‖k‖₊ : NNReal) : ENNReal)) μ)

/-- the spectral radius of a component is at most that of the whole graph. -/
lemma compRho_le {n : ℕ} (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) :
    spectralRadius ℝ (compAdj G c) ≤ spectralRadius ℝ (G.adjMatrix ℝ) := by
  classical
  have hsub : ∀ μ : ℝ, μ ∈ spectrum ℝ (compAdj G c) → μ ∈ spectrum ℝ (G.adjMatrix ℝ) := by
    intro μ hμ
    have hAc : (compAdj G c).IsHermitian := compAdj_isHermitian G c
    rcases exists_eigenvalue_of_mem_spectrum_any (compAdj G c) hAc hμ with ⟨j, hj⟩
    let y : c → ℝ := (hAc.eigenvectorBasis j).ofLp
    have hy0 : y ≠ 0 := by
      intro hy0'
      have hd := eigenvector_dotProduct_self_any (compAdj G c) hAc j
      change y ⬝ᵥ y = 1 at hd
      rw [hy0'] at hd
      simp at hd
    have hAy : (compAdj G c) *ᵥ y = μ • y := by
      have h1 := Matrix.IsHermitian.mulVec_eigenvectorBasis hAc j
      dsimp [y]
      rw [h1, hj]
    rcases eigen_component_of G c hy0 hAy with ⟨x, hx0, hAx⟩
    exact eigen_mem_spectrum (G.adjMatrix ℝ) hx0 hAx
  unfold spectralRadius
  apply iSup_le
  intro μ
  apply iSup_le
  intro hμ
  have hμ' : μ ∈ spectrum ℝ (G.adjMatrix ℝ) := hsub μ hμ
  exact le_trans
    (le_iSup (fun _ : μ ∈ spectrum ℝ (G.adjMatrix ℝ) => ((‖μ‖₊ : NNReal) : ENNReal)) hμ')
    (le_iSup (fun k : ℝ => ⨆ _ : k ∈ spectrum ℝ (G.adjMatrix ℝ), ((‖k‖₊ : NNReal) : ENNReal)) μ)

/-- a chosen vertex of a connected component. -/
noncomputable def compAnchor {n : ℕ} (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) :
    Fin n :=
  Classical.choose (SimpleGraph.ConnectedComponent.nonempty_supp c)

/-- the chosen vertex belongs to the component. -/
lemma compAnchor_mem {n : ℕ} (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) :
    compAnchor G c ∈ c.supp := by
  exact Classical.choose_spec (SimpleGraph.ConnectedComponent.nonempty_supp c)

/-- decoupling (classical-instance version of `Components.lamI_sub_adj_restrict`): restriction
to a component of `(lam0I−A_G)x` equals `(lam0I−A_c)(x|_c)`. -/
lemma lamI_sub_adj_restrict_comp {n : ℕ} (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent)
    {lam0 : ℝ} (x : Fin n → ℝ) :
    compRest G c ((lam0 • (1 : Matrix (Fin n) (Fin n) ℝ) - (G.adjMatrix ℝ)) *ᵥ x)
      = (lam0 • (1 : Matrix c c ℝ) - compAdj G c) *ᵥ compRest G c x := by
  classical
  funext v
  have h1 := adj_restrict_mem G c x v
  simp only [compRest, compAdj]
  have hlam1 : ((lam0 • (1 : Matrix (Fin n) (Fin n) ℝ) - (G.adjMatrix ℝ)) *ᵥ x) v.1
      = lam0 * x v.1 - ((G.adjMatrix ℝ) *ᵥ x) v.1 := by
    rw [mulVec_sub_any]
    simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.one_apply]
  have hlam2 : ((lam0 • (1 : Matrix c c ℝ) - (cGraph G c).adjMatrix ℝ) *ᵥ compRest G c x) v
      = lam0 * (compRest G c x) v - ((cGraph G c).adjMatrix ℝ *ᵥ compRest G c x) v := by
    rw [mulVec_sub_any]
    simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Matrix.one_apply]
  rw [hlam1, hlam2, h1]
  simp [compRest]

/-- if `x` is in the kernel of `lam0I − A_G` then its restriction to any component is in the
kernel of `lam0I − A_c` (classical-instance version). -/
lemma compRest_ker_comp {n : ℕ} (G : SimpleGraph (Fin n)) (c : G.ConnectedComponent) {lam0 : ℝ}
    (x : Fin n → ℝ) (hx : ((lam0 • (1 : Matrix (Fin n) (Fin n) ℝ) - (G.adjMatrix ℝ)) *ᵥ x) = 0) :
    ((lam0 • (1 : Matrix c c ℝ) - compAdj G c) *ᵥ compRest G c x) = 0 := by
  classical
  have h := lamI_sub_adj_restrict_comp G c (lam0 := lam0) (x := x)
  rw [hx] at h
  have h0 : compRest G c (0 : Fin n → ℝ) = 0 := by
    funext v
    rfl
  rw [h0] at h
  exact h.symm

/-- nullity of `λI − A_G` is at most the number of components with spectral radius λ. -/
lemma b1_nullity_le {α : ℝ} {n : ℕ} (G : SimpleGraph (Fin n))
    (hα0 : 0 < α) (hα1 : α < 1) (hn : 0 < n)
    (hρ : spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal (lam α)) :
    Module.finrank ℝ (LinearMap.ker
        (((lam α • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ).mulVecLin)))
      ≤ Fintype.card {c : G.ConnectedComponent //
          spectralRadius ℝ (compAdj G c) = ENNReal.ofReal (lam α)} := by
  classical
  let lamv : ℝ := lam α
  have hlamv : 0 < lamv := by simpa [lamv] using (lam_pos hα0 hα1)
  let B : Matrix (Fin n) (Fin n) ℝ := lamv • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ
  let K : Submodule ℝ (Fin n → ℝ) := LinearMap.ker B.mulVecLin
  let J : Type := {c : G.ConnectedComponent // spectralRadius ℝ (compAdj G c) = ENNReal.ofReal lamv}
  have hle_c : ∀ c : G.ConnectedComponent, spectralRadius ℝ (compAdj G c) ≤ ENNReal.ofReal lamv := by
    intro c
    calc
      spectralRadius ℝ (compAdj G c) ≤ spectralRadius ℝ (G.adjMatrix ℝ) := compRho_le G c
      _ = ENNReal.ofReal lamv := by simpa [lamv] using hρ
  have hB_of_mem : ∀ z : K, B *ᵥ z.1 = 0 := by
    intro z
    change B.mulVecLin z.1 = 0
    exact z.2
  -- on a component whose spectral radius is below lamv, kernel vectors restrict to zero
  have hzcomp : ∀ (c : G.ConnectedComponent) (x : Fin n → ℝ), B *ᵥ x = 0 →
      spectralRadius ℝ (compAdj G c) < ENNReal.ofReal lamv → compRest G c x = 0 := by
    intro c x hxB hlt
    by_contra hw
    let w : c → ℝ := compRest G c x
    have hwne : w ≠ 0 := hw
    have hAc : (compAdj G c).IsHermitian := compAdj_isHermitian G c
    have hwk : ((lamv • (1 : Matrix c c ℝ) - compAdj G c) *ᵥ w) = 0 := by
      have hk := compRest_ker_comp G c (lam0 := lamv) (x := x) (by simpa [B, lamv] using hxB)
      simpa [w, compAdj] using hk
    have hAw : (compAdj G c) *ᵥ w = lamv • w := by
      have hlin : lamv • w - (compAdj G c) *ᵥ w = 0 := by
        simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using hwk
      exact (sub_eq_zero.mp hlin).symm
    have hμ : lamv ∈ spectrum ℝ (compAdj G c) := eigen_mem_spectrum (compAdj G c) hwne hAw
    have hval : ENNReal.ofReal |lamv| = ((‖lamv‖₊ : NNReal) : ENNReal) := by
      rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg lamv)]
      rfl
    have hb : ENNReal.ofReal |lamv| ≤ spectralRadius ℝ (compAdj G c) := by
      rw [hval]
      unfold spectralRadius
      exact le_trans
        (le_iSup (fun _ : lamv ∈ spectrum ℝ (compAdj G c) => ((‖lamv‖₊ : NNReal) : ENNReal)) hμ)
        (le_iSup (fun k : ℝ => ⨆ _ : k ∈ spectrum ℝ (compAdj G c), ((‖k‖₊ : NNReal) : ENNReal)) lamv)
    have hlamle : ENNReal.ofReal lamv ≤ spectralRadius ℝ (compAdj G c) := by
      rwa [abs_of_nonneg (le_of_lt hlamv)] at hb
    exact (not_lt_of_ge hlamle) hlt
  let Psi : (Fin n → ℝ) →ₗ[ℝ] (J → ℝ) :=
    { toFun := fun x t => x (compAnchor G t.1)
      map_add' := by intro x y; funext t; rfl
      map_smul' := by intro a x; funext t; rfl }
  let F : K →ₗ[ℝ] (J → ℝ) := Psi.comp K.subtype
  have hker0 : ∀ z : K, F z = 0 → z = 0 := by
    intro z hz
    apply Subtype.ext
    apply funext
    intro v
    let c := G.connectedComponentMk v
    have hv : v ∈ c.supp := by
      simp [c, SimpleGraph.ConnectedComponent.mem_supp_iff]
    have hBz : B *ᵥ z.1 = 0 := hB_of_mem z
    by_cases hJ : spectralRadius ℝ (compAdj G c) = ENNReal.ofReal lamv
    · have hzt : z.1 (compAnchor G c) = 0 := by
        have hfun : Psi z.1 = 0 := by
          simpa [F, Psi] using hz
        simpa [Psi] using congrFun hfun ⟨c, hJ⟩
      have hAc : (compAdj G c).IsHermitian := compAdj_isHermitian G c
      have hnn : ∀ i j : c, 0 ≤ (compAdj G c) i j := compAdj_nonneg G c
      have hcard : 0 < Fintype.card c := compCard_pos G c
      rcases nonneg_eigenvector_of_spectralRadius_any hcard (compAdj G c) hAc hnn hlamv hJ with
        ⟨u, hu_nonneg, hu_sum, hu_eig⟩
      have hu_ne : u ≠ 0 := by
        intro hu0
        have hs : 0 < (0 : ℝ) := by simpa [hu0] using hu_sum
        norm_num at hs
      have hu_pos : ∀ i : c, 0 < u i := positive_eigenvector_of_connected_any
        (fun a b : c => compReachable G c a b) hu_nonneg hu_ne hu_eig
      let w : c → ℝ := compRest G c z.1
      have hwk : ((lamv • (1 : Matrix c c ℝ) - compAdj G c) *ᵥ w) = 0 := by
        have hk := compRest_ker_comp G c (lam0 := lamv) (x := z.1) (by simpa [B, lamv] using hBz)
        simpa [w, compAdj] using hk
      have hAw : (compAdj G c) *ᵥ w = lamv • w := by
        have hlin : lamv • w - (compAdj G c) *ᵥ w = 0 := by
          simpa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using hwk
        exact (sub_eq_zero.mp hlin).symm
      rcases eigenspace_eq_span_of_positive_any
          (fun a b : c => compReachable G c a b) hu_nonneg hu_ne hu_eig w hAw with ⟨s, hws⟩
      let a : c := ⟨compAnchor G c, compAnchor_mem G c⟩
      have hsa0 : s = 0 := by
        have huapos : 0 < u a := hu_pos a
        have hwacon : w a = 0 := by
          simpa [w, compRest, a] using hzt
        have hmul : s * u a = 0 := by
          calc
            s * u a = (s • u) a := by simp [Pi.smul_apply]
            _ = w a := by rw [hws]
            _ = 0 := hwacon
        exact (mul_eq_zero.mp hmul).resolve_right (ne_of_gt huapos)
      have hwv : w ⟨v, hv⟩ = 0 := by
        rw [hws]
        have hzero_vec : s • u = 0 := by rw [hsa0]; simp
        exact congrFun hzero_vec ⟨v, hv⟩
      simpa [w, compRest] using hwv
    · have hlt : spectralRadius ℝ (compAdj G c) < ENNReal.ofReal lamv := by
        exact lt_of_le_of_ne (hle_c c) hJ
      have hw0 := hzcomp c z.1 hBz hlt
      simpa [compRest] using congrFun hw0 ⟨v, hv⟩
  have hF : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    let z : K := x - y
    have hFz : F z = 0 := by
      change F (x - y) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr hxy
    have hz0 : z = 0 := hker0 z hFz
    have hd : x.1 - y.1 = 0 := by simpa [z] using congrArg (fun w : K => w.1) hz0
    exact sub_eq_zero.mp hd
  have hdim : Module.finrank ℝ K ≤ Fintype.card J := by
    have hle := LinearMap.finrank_le_finrank_of_injective (f := F) hF
    have hJ : Module.finrank ℝ (J → ℝ) = Fintype.card J := by
      exact Module.finrank_pi ℝ
    exact le_trans hle (le_of_eq hJ)
  rw [Fintype.card_subtype] at hdim
  rw [Fintype.card_subtype]
  simpa [K, B, lamv] using hdim

/-- components with spectral radius λ have at least k₀ vertices, and n ≥ k₀ · |J|. -/
lemma b1_card_ge {lam0 : ℝ} {n : ℕ} (G : SimpleGraph (Fin n))
    (hk : spectralRadiusOrder lam0 < (⊤ : ℕ∞))
    (hρ : spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal lam0) :
    (Fintype.card {c : G.ConnectedComponent //
          spectralRadius ℝ (compAdj G c) = ENNReal.ofReal lam0}) * (spectralRadiusOrder lam0).toNat
      ≤ n := by
  classical
  let k0 : ℕ := (spectralRadiusOrder lam0).toNat
  let J : Type := {c : G.ConnectedComponent // spectralRadius ℝ (compAdj G c) = ENNReal.ofReal lam0}
  have hkle : ∀ t : J, k0 ≤ Fintype.card ↥(t.1) := by
    intro t
    have hρc : spectralRadius ℝ ((cGraph G (t.1)).adjMatrix ℝ) = ENNReal.ofReal lam0 := by
      simpa [compAdj] using t.2
    have h := spectralRadiusOrder_toNat_le_card (G := cGraph G (t.1)) hρc
    simpa [k0] using h
  have hsumconst : (∑ t : J, k0) = Fintype.card J * k0 := by
    simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hsum : Fintype.card J * k0 ≤ ∑ t : J, Fintype.card ↥(t.1) := by
    calc
      Fintype.card J * k0 = ∑ t : J, k0 := hsumconst.symm
      _ ≤ ∑ t : J, Fintype.card ↥(t.1) := Finset.sum_le_sum (fun t ht => hkle t)
  have hsigma_le : (∑ t : J, Fintype.card ↥(t.1)) ≤ n := by
    have hσ : (∑ t : J, Fintype.card ↥(t.1)) = Fintype.card (Σ t : J, ↥(t.1)) := by
      exact (Fintype.card_sigma).symm
    rw [hσ]
    have hinj : Function.Injective (fun p : (Σ t : J, ↥(t.1)) => p.2.1) := by
      intro p q hpq
      change p.snd.val = q.snd.val at hpq
      apply Sigma.ext
      · apply Subtype.ext
        apply SimpleGraph.ConnectedComponent.eq_of_common_vertex (v := p.snd.val)
        · exact p.snd.property
        · rw [hpq]
          exact q.snd.property
      · have hp : p.fst = q.fst := by
          apply Subtype.ext
          apply SimpleGraph.ConnectedComponent.eq_of_common_vertex (v := p.snd.val)
          · exact p.snd.property
          · rw [hpq]
            exact q.snd.property
        have hc : (p.fst : G.ConnectedComponent) = (q.fst : G.ConnectedComponent) := by
          exact congrArg (fun t : J => (t : G.ConnectedComponent)) hp
        have hpred : ∀ x : Fin n, x ∈ (p.fst : G.ConnectedComponent).supp
            ↔ x ∈ (q.fst : G.ConnectedComponent).supp := by
          intro x
          rw [hc]
        rw [Subtype.heq_iff_coe_eq hpred]
        exact hpq
    have hle := Fintype.card_le_of_injective (fun p : (Σ t : J, ↥(t.1)) => p.2.1) hinj
    simpa using hle
  have hmain : Fintype.card J * k0 ≤ n := le_trans hsum hsigma_le
  rw [Fintype.card_subtype] at hmain
  rw [Fintype.card_subtype]
  simpa [k0] using hmain

/-- Case B1 upper bound: `n ≤ k₀(d−1)/(k₀−1)`. -/
theorem b1_bound {α : ℝ} {n d : ℕ} (v : Fin n → Euc d)
    (hα0 : 0 < α) (hα1 : α < 1) (hn : 0 < n)
    (hvnorm : ∀ i, ‖v i‖ = 1)
    (hvangle : ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α)
    (hk : spectralRadiusOrder (lam α) < (⊤ : ℕ∞))
    (hρ : spectralRadius ℝ ((assocGraph α v).adjMatrix ℝ) = ENNReal.ofReal (lam α)) :
    (n : ℝ) ≤ ((((spectralRadiusOrder (lam α)).toNat) * (d - 1) : ℝ))
      / ((((spectralRadiusOrder (lam α)).toNat) - 1 : ℝ)) := by
  classical
  let G : SimpleGraph (Fin n) := assocGraph α v
  let lam0 : ℝ := lam α
  let k0 : ℕ := (spectralRadiusOrder lam0).toNat
  let B : Matrix (Fin n) (Fin n) ℝ := lam0 • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ
  let K : Submodule ℝ (Fin n → ℝ) := LinearMap.ker B.mulVecLin
  let rk : ℕ := B.rank
  let nu : ℕ := Module.finrank ℝ K
  have hlam0 : 0 < lam0 := by simpa [lam0] using (lam_pos hα0 hα1)
  have hk2 : 2 ≤ k0 := by
    simpa [k0, lam0] using (spectralRadiusOrder_toNat_ge_two hlam0 (by simpa [lam0] using hk))
  have hrn : rk + nu = n := by
    dsimp [rk, nu, K, B]
    exact rank_add_nullity_eq n (lam α • (1 : Matrix (Fin n) (Fin n) ℝ) - G.adjMatrix ℝ)
  have hrb : rk ≤ d - 1 := by
    dsimp [rk, B, G, lam0]
    simpa using (b1_rank_le_d_sub_one v hα0 hα1 hn hvnorm hvangle hρ)
  have hnull0 := b1_nullity_le G hα0 hα1 hn hρ
  have hcb0 := b1_card_ge (lam0 := lam α) G hk hρ
  rw [Fintype.card_subtype] at hnull0
  rw [Fintype.card_subtype] at hcb0
  let S : Finset G.ConnectedComponent := Finset.univ.filter
    (fun c => spectralRadius ℝ (compAdj G c) = ENNReal.ofReal (lam α))
  let q : ℕ := S.card
  have hnull : nu ≤ q := by
    dsimp [q, S]
    simpa [G] using hnull0
  have hcb : q * k0 ≤ n := by
    dsimp [q, S]
    simpa [G] using hcb0
  have hN : (rk : ℝ) + (nu : ℝ) = (n : ℝ) := by exact_mod_cast hrn
  have hr : (rk : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by exact_mod_cast hrb
  have ht : (nu : ℝ) ≤ (q : ℝ) := by exact_mod_cast hnull
  have hq : (q : ℝ) * (k0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcb
  have hk2r : (2 : ℝ) ≤ (k0 : ℝ) := by exact_mod_cast hk2
  have hmain : (n : ℝ) * ((k0 : ℝ) - 1) ≤ (k0 : ℝ) * ((d - 1 : ℕ) : ℝ) := by
    nlinarith
  have hkpos : 0 < (k0 : ℝ) - 1 := by
    have : 1 < (k0 : ℝ) := by linarith
    linarith
  have hgoal0 : (n : ℝ) ≤ ((k0 : ℝ) * ((d - 1 : ℕ) : ℝ)) / ((k0 : ℝ) - 1) := by
    exact (le_div_iff₀ hkpos).mpr hmain
  by_cases hd1 : 1 ≤ d
  · have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub hd1]
      norm_num
    rw [← hcast]
    exact hgoal0
  · exfalso
    have hd0 : d = 0 := by omega
    subst d
    have hNpos : 0 < (n : ℝ) := by exact_mod_cast hn
    simp at hgoal0
    linarith

end
end Submission
