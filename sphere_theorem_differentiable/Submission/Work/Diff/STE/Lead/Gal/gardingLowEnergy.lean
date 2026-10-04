import Mathlib
import Submission.Work.Diff.STE.Lead.Gal.gardClauses
import Submission.Work.Diff.STE.Lead.Gal.gardJet_holds
import Submission.Work.Diff.STE.Lead.Gal.gardPerENormSq
import Submission.Work.Diff.STE.Lead.Gal.pdVec_ofReal_eq_pdRVec
import Submission.Work.Diff.STE.B3.Rres_eq_residualLow
import Submission.Work.Diff.STE.B3.iteratedFDeriv_fderiv_le_of_pdVec
import Submission.Work.Diff.STE.B3.Recon
import Submission.Work.Diff.STE.B3.transport_Rres_contDiffOn

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.Gal

/-
ROUTE.  Notation: `Idx := Fin (Module.finrank ℝ E)`, `P := deTurckSec hLC g₀ h …`,
`Rb := D.R j h a b`, `Pb := D.R j P a b`.

1. `R j P a b` is supported in the *closed* `σ j`-ball and `D.Rper j P a b = R j P a b` on the open
   cube (`Work.Diff.STE.B3Data.R_support`, `Rper_eq_R`, `B3Data.hσ2 : 2 * σ j ≤ 1/4`), so the
   integrals defining `ENormSq` only see the `σ j`-ball.
2. On `‖z‖ ≤ 2 σ j`, `D.R j P a b z = Σ_{pq} ((Gf j z)⁻¹)_{pq} ∂_p∂_q (R j h a b) z
   + residualLow D h j z a b` (`Work.Diff.STE.B3.Rres_eq_residualLow`, PROVED).  On the smaller
   ball `‖z‖ ≤ σ j` one has `((Gf)⁻¹) = A` (`hA`) and `residualLow = Ψ` (`hP`).
3. Consequently, for `‖z‖ ≤ σ j` and each `m ≤ k-1`, `β : Fin m → Idx`,
   `pdVec m β (R j P a b) z = Σ_{pq} pdVec-binom(A p q -jump, ∂_p∂_q Rb -jump) + pdVec m β (Ψ a b) z`,
   bounded by `Work.Diff.STE.Lead.Gal.pdVec_mul_le` (PROVED, the iterated Leibniz rule) with
   * `hA`'s jet bound `CA` for the `A`-factors,
   * the Clairaut reordering `pdVec m β (pd c (pd d u)) = pdVec (m+2) (Fin.cons c (Fin.cons d β)) u`
     together with `GardJet` (`gardJet_holds`, PROVED) for the `Rb`-factors — this needs
     `ContDiffAt.isSymmSndFDerivAt` + `IsSymmSndFDerivAt.iteratedFDeriv_cons` (Mathlib) to commute
     the partials, or `Work.Diff.STE.Lead.Gal.pdR_clairaut`,
   * `hP`'s jet bound `CR` for the `Ψ`-factor.
   Outside the `σ j`-ball `pdVec m β (R j P a b) z = 0` (support), so the bound is global.
4. Squaring and integrating over the (volume `1`) unit cube gives `ENormSq m (Rper j P a b) ≤
   (Fintype.card (Fin m → Idx)) * C₀ ^ 2` with `C₀` independent of `h` (this is
   `Work.Diff.STE.Lead.Gal.ENormSq_le_of_sup_bound_b` from `gardRjBridge.lean`, or re-derive).
   Taking `CL := (card (Fin (k-1) → Idx) + card (Fin 0 → Idx)) * C₀ ^ 2` and using
   `0 ≤ ENormSq (k+1) (Rper j h a b)` finishes.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

local notation "Idx" => Fin (Module.finrank ℝ E)

/-! ## 1. Bridges between the complex and the real iterated partial derivatives -/

/-- `pd p (pd q ·)` is `pdVec` along the two-tuple `(p, q)`. -/
lemma gle_pd_pd_eq_pdVec {n : ℕ} (p q : Fin n) (G : (Fin n → ℝ) → ℂ) :
    Work.Diff.STE.pd p (Work.Diff.STE.pd q G)
      = Work.Diff.STE.pdVec 2 (Fin.cons p (Fin.cons q (Fin.elim0))) G := by
  simp only [Work.Diff.STE.pdVec, Work.Diff.STE.pdList, List.ofFn_cons, List.ofFn_zero,
    List.foldr_cons, List.foldr_nil]

/-- **The complex iterated partial derivatives of a real function.**  For `f : (Fin n → ℝ) → ℝ`
the complexification of `∂_p∂_q f` is `∂_p∂_q` of the complexification of `f`.  No smoothness
hypothesis is needed (`fderiv` of a non-differentiable function is the junk value `0`, and the
complexification is differentiable exactly where the function is). -/
lemma gle_pd_pd_ofReal {n : ℕ} (p q : Fin n) (f : (Fin n → ℝ) → ℝ) :
    Work.Diff.STE.pd p (Work.Diff.STE.pd q (fun y => ((f y : ℝ) : ℂ)))
      = fun y => ((Work.Diff.STE.pdR p (Work.Diff.STE.pdR q f) y : ℝ) : ℂ) := by
  rw [gle_pd_pd_eq_pdVec p q (fun y => ((f y : ℝ) : ℂ)),
    pdVec_ofReal_eq_pdRVec 2 (Fin.cons p (Fin.cons q (Fin.elim0))) f]
  funext y
  congr 1

/-- **Differentiating a real function costs one derivative index**, with no loss in the constant:
if all `pdVec`-jets of the complexification of `f` up to order `M + 1` are bounded by `Kd` at `z`,
then all `pdVec`-jets of the complexification of `∂_c f` up to order `M` are bounded by `Kd` at `z`.
This is the `pdVec`-level form of the trivial reindexing `∂^β(∂_c f) = ∂^{βc}f`. -/
lemma gle_pdVec_pdR_le {n M : ℕ} {f : (Fin n → ℝ) → ℝ} {z : Fin n → ℝ} {c : Fin n} {Kd : ℝ}
    (hjets : ∀ (m : ℕ), m ≤ M + 1 → ∀ β : Fin m → Fin n,
      ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) z‖ ≤ Kd) :
    ∀ (m : ℕ), m ≤ M → ∀ β : Fin m → Fin n,
      ‖Work.Diff.STE.pdVec m β
        (fun y : Fin n → ℝ => ((Work.Diff.STE.pdR c f y : ℝ) : ℂ)) z‖ ≤ Kd := by
  intro m hm β
  have h1 : ‖Work.Diff.STE.pdVec m β
        (fun y : Fin n → ℝ => ((Work.Diff.STE.pdR c f y : ℝ) : ℂ)) z‖
      = ‖Work.Diff.STE.pdVec (m + 1) (Fin.snoc β c)
        (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) z‖ := by
    rw [pdVec_ofReal_eq_pdRVec m β (Work.Diff.STE.pdR c f)]
    simp only []
    rw [Work.Diff.STE.B3.pdRVec_pdR_eq_pdRVec_snoc m β c f]
    rw [pdVec_ofReal_eq_pdRVec (m + 1) (Fin.snoc β c) f]
  rw [h1]
  exact hjets (m + 1) (by omega) (Fin.snoc β c)

/-! ## 2. The transport identity on the `2σ j`-ball -/

/-- `D.R j (deTurckSec …) a b` is the localised weight times the chart value of the DeTurck
operator: the two sides are the same by the definitions of `R`, `mat` and `deTurckSec`. -/
lemma gle_R_deTurckSec
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀) (a b : Idx)
    (z : Idx → ℝ) :
    D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b z
      = Work.Diff.STE.B3.wf (I := I) (M := M) D j z *
          Work.Diff.STE.DeTurck.deTurckOp
            (Work.Diff.STE.D.smetOf (I := I) h hsym hpos hsmooth) g₀ (D.pt j z)
            (D.e j a (D.pt j z)) (D.e j b (D.pt j z)) := by
  simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat, Work.Diff.STE.B3.wf,
    Work.Diff.STE.D.deTurckSec_apply]

/-- **The transport identity, in localised-component form.**  On the closed `2σ j`-ball the
localised component of the DeTurck operator of `h` is the second-order operator with coefficient
`A` (which equals the inverse coordinate-frame chart matrix of `h` there) applied to the localised
component of `h`, plus the residual `residualLow`.  This is
`Work.Diff.STE.B3.Rres_eq_residualLow` read off with the coefficient family `A`. -/
lemma gle_localIdentity_pt
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    (A : Idx → Idx → (Idx → ℝ) → ℝ)
    (hA : ∀ z : Idx → ℝ, ‖z‖ ≤ 2 * D.σ j → ∀ p q : Idx,
      A p q z = ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q)
    {z : Idx → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j) (a b : Idx) :
    D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b z
      = (∑ p, ∑ q, A p q z * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h a b)) z)
        + Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b := by
  have hres := Work.Diff.STE.B3.Rres_eq_residualLow (I := I) (M := M) D hLC h hsym hpos hsmooth
    j hz a b
  have hL : Work.Diff.STE.B3.Rres (I := I) (M := M) D hLC h hsym hpos hsmooth j
      (fun z p q => ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q)
      z a b
      = D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b z
        - (∑ p, ∑ q, ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q
            * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h a b)) z) := rfl
  rw [hL] at hres
  have hsum : (∑ p, ∑ q, A p q z * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h a b)) z)
      = ∑ p, ∑ q, ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q
          * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h a b)) z := by
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hA z hz p q]
  rw [hsum]
  linarith

/-- **The transport identity as a germ, complexified.**  For `‖z‖ ≤ σ j` the localised component of
the DeTurck operator of `h` agrees, near `z`, with the complex second-order operator
`Σ_{cd} A_{cd} ∂_c∂_d` applied to the complexified localised component of `h`, plus the residual
`Ψ` (which equals `residualLow` on the `2σ j`-ball). -/
lemma gle_localIdentity_germ
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    (A : Idx → Idx → (Idx → ℝ) → ℝ)
    (hA : ∀ z : Idx → ℝ, ‖z‖ ≤ 2 * D.σ j → ∀ p q : Idx,
      A p q z = ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) p q)
    (Ψ : Idx → Idx → (Idx → ℝ) → ℂ)
    (hΨ : ∀ (a b : Idx) (z : Idx → ℝ), ‖z‖ ≤ 2 * D.σ j →
      Ψ a b z = ((Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b : ℝ) : ℂ))
    {z : Idx → ℝ} (hz : ‖z‖ ≤ D.σ j) (a b : Idx) :
    (fun y => ((D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b y
        : ℝ) : ℂ))
      =ᶠ[nhds z]
        ((fun y => ∑ c, ∑ d, ((A c d y : ℝ) : ℂ) *
            Work.Diff.STE.pd c (Work.Diff.STE.pd d
              (fun y => ((D.R j h a b y : ℝ) : ℂ))) y)
          + Ψ a b) := by
  have h2 : 0 < 2 * D.σ j - ‖z‖ := by have := D.hσ j; linarith
  filter_upwards [Metric.ball_mem_nhds z h2] with y hy
  have hy2 : ‖y‖ ≤ 2 * D.σ j := by
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have h1 : ‖y‖ ≤ ‖y - z‖ + ‖z‖ := by simpa using norm_add_le (y - z) z
    linarith
  have hpt := gle_localIdentity_pt (I := I) (M := M) D hLC h hsym hpos hsmooth j A hA hy2 a b
  have hA1 : ((∑ p, ∑ q, A p q y * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q
        (D.R j h a b)) y : ℝ) : ℂ)
      = ∑ c, ∑ d, ((A c d y : ℝ) : ℂ) *
          Work.Diff.STE.pd c (Work.Diff.STE.pd d
            (fun y => ((D.R j h a b y : ℝ) : ℂ))) y := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Complex.ofReal_mul, gle_pd_pd_ofReal p q (D.R j h a b)]
  show ((D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b y
      : ℝ) : ℂ)
      = (∑ c, ∑ d, ((A c d y : ℝ) : ℂ) *
          Work.Diff.STE.pd c (Work.Diff.STE.pd d
            (fun y => ((D.R j h a b y : ℝ) : ℂ))) y) + Ψ a b y
  rw [hpt, Complex.ofReal_add, hA1, ← hΨ a b y hy2]

/-! ## 3. The composite jet bound

A colleague is proving the same statement as `gle_jbl` under the name
`Work.Diff.STE.Lead.Gal.jet_bound_of_localIdentity` (module
`Submission.Work.Diff.STE.Lead.Gal.jet_bound_of_localIdentity`); the copy below keeps this file
self-contained. -/

/-- `pdVec` is additive over the sum of two globally smooth functions. -/
private lemma gle_pdVec_add {n m : ℕ} {f g : (Fin n → ℝ) → ℂ} {x : Fin n → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞)) f) (hg : ContDiff ℝ ((⊤ : ℕ∞)) g) (β : Fin m → Fin n) :
    Work.Diff.STE.pdVec m β (fun y => f y + g y) x
      = Work.Diff.STE.pdVec m β f x + Work.Diff.STE.pdVec m β g x := by
  have h := Work.Diff.STE.csqp_pdVec_finset_sum (j := m) β (Finset.univ : Finset (Fin 2))
    (fun i : Fin 2 => if i = 0 then f else g) x ?_
  · simpa [Fin.sum_univ_two] using h
  · intro i _
    by_cases hi : i = 0
    · rw [if_pos hi]; exact hf
    · rw [if_neg hi]; exact hg

/-- `pdVec` is additive over a double sum of globally smooth functions. -/
private lemma gle_pdVec_sum2 {n m : ℕ} {h : Fin n → Fin n → (Fin n → ℝ) → ℂ} {x : Fin n → ℝ}
    (hh : ∀ c d, ContDiff ℝ ((⊤ : ℕ∞)) (h c d)) (β : Fin m → Fin n) :
    Work.Diff.STE.pdVec m β (fun y => ∑ c, ∑ d, h c d y) x
      = ∑ c, ∑ d, Work.Diff.STE.pdVec m β (h c d) x := by
  have houter := Work.Diff.STE.csqp_pdVec_finset_sum (j := m) β
    (Finset.univ : Finset (Fin n)) (fun c => fun y => ∑ d, h c d y) x ?_
  · rw [houter]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Work.Diff.STE.csqp_pdVec_finset_sum (j := m) β (Finset.univ : Finset (Fin n))
      (fun d => h c d) x (fun d _ => hh c d)]
  · intro c _
    exact ContDiff.sum (fun d _ => hh c d)

/-- **The composite jet bound.**  If a function `F` agrees near `z` with the second-order
operator `Σ_{cd} A_{cd} ∂_c∂_d G` applied to `G` plus a residual `Ψ`, then all the `pdVec`-jets of
`F` of order `≤ N` at `z` are bounded by a constant (depending only on `n` and `N`) times
`CA * CD + CR + 1`, where `CA` bounds the jets of the coefficients, `CD` those of the second
derivatives of `G` and `CR` those of the residual. -/
private theorem gle_jbl {n N : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F G Ψ : (Fin n → ℝ) → ℂ)
        (A : Fin n → Fin n → (Fin n → ℝ) → ℂ) (z : Fin n → ℝ)
        (CA KG CR CD : ℝ), 0 ≤ CA → 0 ≤ KG → 0 ≤ CR → 0 ≤ CD →
        (∀ c d, ContDiff ℝ ((⊤ : ℕ∞)) (A c d)) →
        ContDiff ℝ ((⊤ : ℕ∞)) G →
        ContDiff ℝ ((⊤ : ℕ∞)) Ψ →
        F =ᶠ[nhds z] ((fun y : Fin n → ℝ =>
            ∑ c, ∑ d, A c d y * Work.Diff.STE.pd c (Work.Diff.STE.pd d G) y) + Ψ) →
        (∀ (c d : Fin n) (m : ℕ), m ≤ N → ∀ β : Fin m → Fin n,
          ‖Work.Diff.STE.pdVec m β (A c d) z‖ ≤ CA) →
        (∀ (m : ℕ), m ≤ N + 2 → ∀ β : Fin m → Fin n,
          ‖Work.Diff.STE.pdVec m β G z‖ ≤ KG) →
        (∀ (m : ℕ), m ≤ N → ∀ β : Fin m → Fin n,
          ‖Work.Diff.STE.pdVec m β Ψ z‖ ≤ CR) →
        (∀ (c d : Fin n) (m : ℕ), m ≤ N → ∀ β : Fin m → Fin n,
          ‖Work.Diff.STE.pdVec m β (Work.Diff.STE.pd c (Work.Diff.STE.pd d G)) z‖ ≤ CD) →
        ∀ (m : ℕ), m ≤ N → ∀ β : Fin m → Fin n,
          ‖Work.Diff.STE.pdVec m β F z‖ ≤ C * (CA * CD + CR + 1) := by
  refine ⟨(n : ℝ) ^ 2 * ((2 : ℝ) ^ N * ((n : ℝ) + 1) ^ N * ((N : ℝ) + 1)) + 1, by positivity, ?_⟩
  intro F G Ψ A z CA KG CR CD hCA hKG hCR hCD hAsm hGsm hΨsm hgerm hAj hGj hΨj hCDj m hm β
  set LB : ℝ := (2 : ℝ) ^ N * ((n : ℝ) + 1) ^ N * ((N : ℝ) + 1) with hLB
  have hLB0 : 0 ≤ LB := by rw [hLB]; positivity
  -- smoothness of the second partial derivatives of `G`
  have hDsm : ∀ c d : Fin n, ContDiff ℝ ((⊤ : ℕ∞))
      (Work.Diff.STE.pd c (Work.Diff.STE.pd d G)) := by
    intro c d
    have h := Work.Diff.STE.csqp_contDiff_pdList_top [c, d] hGsm
    simpa only [Work.Diff.STE.pdList, List.foldr_cons, List.foldr_nil] using h
  -- smoothness of the summands and of the sum
  have hTsm : ∀ c d : Fin n, ContDiff ℝ ((⊤ : ℕ∞))
      (fun y : Fin n → ℝ => A c d y * Work.Diff.STE.pd c (Work.Diff.STE.pd d G) y) :=
    fun c d => (hAsm c d).mul (hDsm c d)
  have hSsm : ContDiff ℝ ((⊤ : ℕ∞))
      (fun y : Fin n → ℝ => ∑ c, ∑ d, A c d y * Work.Diff.STE.pd c (Work.Diff.STE.pd d G) y) :=
    ContDiff.sum fun c _ => ContDiff.sum fun d _ => hTsm c d
  -- pass to the sum, and split it
  rw [Work.Diff.STE.csqp_pdVec_congr β hgerm]
  have huncurry : Work.Diff.STE.pdVec m β
        ((fun y : Fin n → ℝ => ∑ c, ∑ d, A c d y * Work.Diff.STE.pd c
            (Work.Diff.STE.pd d G) y) + Ψ) z
      = Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => (∑ c, ∑ d, A c d y *
            Work.Diff.STE.pd c (Work.Diff.STE.pd d G) y) + Ψ y) z := rfl
  rw [huncurry, gle_pdVec_add hSsm hΨsm β, gle_pdVec_sum2 hTsm β]
  -- the Leibniz bound on each summand
  have hterm : ∀ c d : Fin n,
      ‖Work.Diff.STE.pdVec m β
        (fun y : Fin n → ℝ => A c d y * Work.Diff.STE.pd c (Work.Diff.STE.pd d G) y) z‖
        ≤ LB * (CA * CD) := by
    intro c d
    have h := pdVec_mul_le (F := A c d)
      (G := Work.Diff.STE.pd c (Work.Diff.STE.pd d G)) (A := CA) (B := CD)
      hCA hCD (hAsm c d) (hDsm c d)
      (fun j hj γ => hAj c d j hj γ) (fun j hj γ => hCDj c d j hj γ) m hm β
    rwa [hLB]
  have hnn : 0 ≤ LB * (CA * CD) := mul_nonneg hLB0 (mul_nonneg hCA hCD)
  -- assemble
  have hsum := Finset.sum_le_sum fun c (_ : c ∈ (Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum fun d (_ : d ∈ (Finset.univ : Finset (Fin n))) => hterm c d
  have hcard : (∑ _c : Fin n, ∑ _d : Fin n, LB * (CA * CD))
      = (n : ℝ) ^ 2 * (LB * (CA * CD)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
    ring
  have h1 : ‖∑ c, ∑ d, Work.Diff.STE.pdVec m β
        (fun y : Fin n → ℝ => A c d y * Work.Diff.STE.pd c (Work.Diff.STE.pd d G) y) z‖
      ≤ (n : ℝ) ^ 2 * (LB * (CA * CD)) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun c _ => norm_sum_le _ _).trans ?_)
    exact hsum.trans (le_of_eq hcard)
  have h2 : ‖Work.Diff.STE.pdVec m β Ψ z‖ ≤ CR := hΨj m hm β
  have h3 : ‖(∑ c, ∑ d, Work.Diff.STE.pdVec m β
        (fun y : Fin n → ℝ => A c d y * Work.Diff.STE.pd c (Work.Diff.STE.pd d G) y) z)
        + Work.Diff.STE.pdVec m β Ψ z‖ ≤ (n : ℝ) ^ 2 * (LB * (CA * CD)) + CR :=
    (norm_add_le _ _).trans (add_le_add h1 h2)
  refine h3.trans ?_
  have hCDnn : 0 ≤ CA * CD := mul_nonneg hCA hCD
  have hnn2 : 0 ≤ (n : ℝ) ^ 2 * LB := by positivity
  nlinarith [hCDnn, hCR, hnn2]

/-! ## 4. The energy bound -/

/-- **`GardL`.**  The `H^{k-1}` and `L²` energies of the localised DeTurck operator of `h` are
bounded by a constant times `1 + H^{k+1}(h)`, with a constant uniform in the section `h`, in the
chart `j` and in the frame indices. -/
theorem gle_gardL
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (k : ℕ) (hk : 1 ≤ k)
    (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K)
    (hA : Work.Diff.STE.Lead.Gal.GardA (I := I) (M := M) D k lam K)
    (hP : Work.Diff.STE.Lead.Gal.GardP (I := I) (M := M) D k lam K) :
    Work.Diff.STE.Lead.Gal.GardL (I := I) (M := M) D hLC k lam K := by
  classical
  obtain ⟨lam', CA, hlam'0, hCA0, hAcl⟩ := hA
  obtain ⟨CR, hCR0, hPcl⟩ := hP
  obtain ⟨W, hW0, hW⟩ := exists_weight_jets (I := I) (M := M) D (k + 1)
  obtain ⟨CB, hCB0, hCBl⟩ := gle_jbl (n := Module.finrank ℝ E) (N := k - 1)
  obtain ⟨CE, hCE0, hCEl⟩ := gardPerENormSq (n := Module.finrank ℝ E) (k - 1) (1 / 8)
    (by norm_num) (by norm_num)
  set KG : ℝ := (2 : ℝ) ^ (k + 1) * ((Module.finrank ℝ E : ℝ) + 1) ^ (k + 1)
    * (((k + 1 : ℕ) : ℝ) + 1) * (W * K) with hKGdef
  have hKG0 : 0 ≤ KG := by rw [hKGdef]; positivity
  have hC00 : 0 ≤ CB * (CA * KG + CR + 1) := by positivity
  refine ⟨2 * (CE * (CB * (CA * KG + CR + 1)) ^ 2) + 1, by positivity, ?_⟩
  intro h hsym hpos hsmooth hell hub hjet j a b
  -- the three work packages, instantiated
  obtain ⟨A, hAsym, hAell, hAsm, hAper, hAjets, hAeq⟩ :=
    hAcl h hsym hsmooth hell hub hjet j
  obtain ⟨Ps, hPsm, hPsupp, hPjets, hPeq⟩ := hPcl h hsym hsmooth hell hub hjet j
  set P : Work.Diff.STE.Bil (I := I) (M := M) :=
    Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth with hPdef
  -- the DeTurck section has smooth chart data, hence its localised components are smooth
  have hPcd : Work.Diff.STE.D.ChartData (I := I) (M := M) P := by
    rw [hPdef]
    exact Work.Diff.STE.B3.chartData_deTurckSec (I := I) hLC h hsym hpos hsmooth
  have hFsm : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (fun y : Idx → ℝ => ((D.R j P a b y : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D P hPcd j a b)
  have hGsm : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (fun y : Idx → ℝ => ((D.R j h a b y : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hsmooth j a b)
  -- ## Step 1: jets of the localised component of `h` on the `σ j`-ball
  have hKGjets : ∀ w : Idx → ℝ, ‖w‖ ≤ D.σ j → ∀ (m : ℕ), m ≤ k + 1 →
      ∀ β : Fin m → Idx,
      ‖Work.Diff.STE.pdVec m β (fun y : Idx → ℝ => ((D.R j h a b y : ℝ) : ℂ)) w‖ ≤ KG := by
    intro w hw m hm β
    have hjet' : ∀ (i : ι₀) (c d : Idx) (j' : ℕ), j' ≤ k + 1 →
        ∀ (l : Fin j' → Idx) (z : Idx → ℝ), ‖z‖ ≤ 2 * D.σ i →
        ‖Work.Diff.STE.pdVec j' l (fun y : Idx → ℝ => ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K :=
      fun i c d j' hj' l z hz => hjet i j' hj' l z c d hz
    have hmain := jets_component_le (I := I) (M := M) D h hsmooth (k + 1) W K hW0 hK.le hW
      hjet' j a b m hm β w hw
    rwa [hKGdef]
  -- ## Step 2: jets of the second derivatives of the localised component of `h`
  have hCD : ∀ w : Idx → ℝ, ‖w‖ ≤ D.σ j → ∀ (c d : Idx) (m : ℕ), m ≤ k - 1 →
      ∀ β : Fin m → Idx,
      ‖Work.Diff.STE.pdVec m β
        (Work.Diff.STE.pd c (Work.Diff.STE.pd d
          (fun y : Idx → ℝ => ((D.R j h a b y : ℝ) : ℂ)))) w‖ ≤ KG := by
    intro w hw c d m hm β
    have h1 : ∀ (m' : ℕ), m' ≤ k → ∀ β' : Fin m' → Idx,
        ‖Work.Diff.STE.pdVec m' β'
          (fun y : Idx → ℝ => ((Work.Diff.STE.pdR d (D.R j h a b) y : ℝ) : ℂ)) w‖ ≤ KG :=
      fun m' hm' β' => gle_pdVec_pdR_le (M := k) (Kd := KG) (c := d) (f := D.R j h a b)
        (fun m'' hm'' β'' => hKGjets w hw m'' (by omega) β'') m' hm' β'
    rw [gle_pd_pd_ofReal c d (D.R j h a b)]
    refine gle_pdVec_pdR_le (M := k - 1) (Kd := KG) (c := c)
      (f := fun y : Idx → ℝ => Work.Diff.STE.pdR d (D.R j h a b) y)
      (fun m' hm' β' => h1 m' (by omega) β') m hm β
  -- ## Step 3: the jet bound of `R j (P h) a b` on the `σ j`-ball
  have hJBL := hCBl
  have hC0jets : ∀ w : Idx → ℝ, ‖w‖ ≤ D.σ j → ∀ (m : ℕ), m ≤ k - 1 →
      ∀ β : Fin m → Idx,
      ‖Work.Diff.STE.pdVec m β
        (fun y : Idx → ℝ => ((D.R j P a b y : ℝ) : ℂ)) w‖
        ≤ CB * (CA * KG + CR + 1) := by
    intro w hw m hm β
    have hgerm := gle_localIdentity_germ (I := I) (M := M) D hLC h hsym hpos hsmooth j A
      (fun z hz p q => hAeq z hz p q) Ps (fun a' b' z hz => hPeq a' b' z hz) hw a b
    exact hJBL (fun y : Idx → ℝ => ((D.R j P a b y : ℝ) : ℂ))
      (fun y : Idx → ℝ => ((D.R j h a b y : ℝ) : ℂ)) (Ps a b)
      (fun c d y => ((A c d y : ℝ) : ℂ)) w CA KG CR KG hCA0 hKG0 hCR0 hKG0
      (fun c d => Complex.ofRealCLM.contDiff.comp (hAsm c d)) hGsm (hPsm a b) hgerm
      (fun c d m' hm' β' => hAjets m' (by omega) β' w c d)
      (fun m' hm' β' => hKGjets w hw m' (by omega) β')
      (fun m' hm' β' => hPjets m' (by omega) β' w a b)
      (fun c d m' hm' β' => hCD w hw c d m' hm' β') m hm β
  -- ## Step 4: the same bound on the whole closed `1/8`-ball
  have hts : tsupport (fun y : Idx → ℝ => ((D.R j P a b y : ℝ) : ℂ))
      ⊆ Metric.closedBall (0 : Idx → ℝ) (D.σ j) := by
    refine closure_minimal (fun y hy => ?_) Metric.isClosed_closedBall
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt (by
      have h := support_R_subset_ball (I := I) (M := M) D P j a b hy
      rwa [Metric.mem_ball, dist_zero_right] at h)
  have hbox : ∀ (m : ℕ), m ≤ k - 1 → ∀ β : Fin m → Idx, ∀ w : Idx → ℝ, ‖w‖ ≤ 1 / 8 →
      ‖Work.Diff.STE.pdVec m β (fun y : Idx → ℝ => ((D.R j P a b y : ℝ) : ℂ)) w‖
        ≤ CB * (CA * KG + CR + 1) := by
    intro m hm β w hw
    by_cases hwj : ‖w‖ ≤ D.σ j
    · exact hC0jets w hwj m hm β
    · rw [not_le] at hwj
      have hnot : w ∉ tsupport (fun y : Idx → ℝ => ((D.R j P a b y : ℝ) : ℂ)) := by
        intro hmem
        have h1 := hts hmem
        rw [Metric.mem_closedBall, dist_zero_right] at h1
        linarith
      rw [pdVec_eq_zero_of_notMem_tsupport hnot m β, norm_zero]
      positivity
  have hsupp : Function.support (fun y : Idx → ℝ => ((D.R j P a b y : ℝ) : ℂ))
      ⊆ {z : Idx → ℝ | ∀ i : Idx, z i ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)} := by
    intro y hy i
    rw [Set.mem_Ioo]
    have h1 : ‖y‖ < D.σ j := by
      have h := support_R_subset_ball (I := I) (M := M) D P j a b hy
      rwa [Metric.mem_ball, dist_zero_right] at h
    have h2 : |y i| ≤ ‖y‖ := by
      have := norm_le_pi_norm y i
      rwa [Real.norm_eq_abs] at this
    have h3 := D.hσ2 j
    have h4 : |y i| < 1 / 2 := lt_of_le_of_lt h2 (by linarith)
    exact abs_lt.mp h4
  have hzero : ∀ x : Idx → ℝ, 1 / 8 < ‖x‖ →
      (fun y : Idx → ℝ => ((D.R j P a b y : ℝ) : ℂ)) x = 0 := by
    intro x hx
    have h1 : D.σ j < ‖x‖ := by have h := D.hσ2 j; linarith
    have h2 : x ∉ Function.support (fun y : Idx → ℝ => ((D.R j P a b y : ℝ) : ℂ)) := by
      intro hmem
      have h := support_R_subset_ball (I := I) (M := M) D P j a b hmem
      rw [Metric.mem_ball, dist_zero_right] at h
      linarith
    simpa using h2
  -- ## Step 5: the energies
  have hper : D.Rper j P a b
      = fun z : Idx → ℝ => ∑' q : Idx → ℤ,
          (fun y : Idx → ℝ => ((D.R j P a b y : ℝ) : ℂ)) (z + Work.Diff.STE.iVec q) := rfl
  have hEn := hCEl (fun y : Idx → ℝ => ((D.R j P a b y : ℝ) : ℂ))
    (CB * (CA * KG + CR + 1)) (by positivity) hFsm hsupp hzero hbox (k - 1) (le_refl _)
  have hEn0 := hCEl (fun y : Idx → ℝ => ((D.R j P a b y : ℝ) : ℂ))
    (CB * (CA * KG + CR + 1)) (by positivity) hFsm hsupp hzero hbox 0 (by omega)
  rw [← hper] at hEn hEn0
  have hnonneg : 0 ≤ Work.Diff.STE.ENormSq (k + 1) (D.Rper j h a b) := by
    rw [Work.Diff.STE.ENormSq]
    exact Finset.sum_nonneg fun l _ => MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hCL0 : (0 : ℝ) ≤ 2 * (CE * (CB * (CA * KG + CR + 1)) ^ 2) + 1 := by positivity
  calc Work.Diff.STE.ENormSq (k - 1) (D.Rper j P a b)
        + Work.Diff.STE.ENormSq 0 (D.Rper j P a b)
      ≤ CE * (CB * (CA * KG + CR + 1)) ^ 2
          + CE * (CB * (CA * KG + CR + 1)) ^ 2 := add_le_add hEn hEn0
    _ ≤ (2 * (CE * (CB * (CA * KG + CR + 1)) ^ 2) + 1)
          * (1 + Work.Diff.STE.ENormSq (k + 1) (D.Rper j h a b)) := by
        nlinarith [hCL0, hnonneg]

/-- **`GardL`.**  The `H^{k-1}` and `L²` energies of the localised DeTurck operator of `h` are
bounded by a constant times `1 + H^{k+1}(h)`, with a constant uniform in the section `h`, in the
chart `j` and in the frame indices. -/
theorem gardingLowEnergy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (k : ℕ) (hk : 1 ≤ k)
    (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K)
    (hA : Work.Diff.STE.Lead.Gal.GardA (I := I) (M := M) D k lam K)
    (hP : Work.Diff.STE.Lead.Gal.GardP (I := I) (M := M) D k lam K) :
    Work.Diff.STE.Lead.Gal.GardL (I := I) (M := M) D hLC k lam K :=
  gle_gardL D hLC k hk lam K hlam hK hA hP

end

end Work.Diff.STE.Lead.Gal
