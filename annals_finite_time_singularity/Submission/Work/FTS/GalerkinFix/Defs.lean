/-
# GalerkinFix — the CORRECTED N6 interface (ELGINDI / annals_finite_time_singularity)

This directory (`Submission/Work/FTS/GalerkinFix/`, namespace `Work.FTS.GalerkinFix` for the new
mathematics and `Work.FTS.Galerkin` for the corrected interface) is the **fix of the delivered node
N6** (the Galerkin existence theorem of `Submission/Work/FTS/Galerkin/`) requested by the lead on
2026-10-03 (`Submission/Work/FTS/N45_DESIGN_LEAD.md` §1.2–1.3):

| # | old field of `DynInputs` | new shape | reason |
|---|---|---|---|
| 1 | `hApriori` (an estimate *about* solutions of the dynamic equation) | `hLimBound` (the a-priori bound of the **limit** of the Galerkin family) | `hApriori` is not provable as stated: its law has no boundary conditions, so `Φ + h(τ) sin 2θ` is again a solution and the a-priori estimate cannot be bootstrapped (design §0.3) |
| 2 | `hIP : IsH4Inner α IP` (`Construction.IsH4IP` + symmetry: Cauchy–Schwarz with constant `1`, unrestricted bilinearity) | `hIP : Work.FTS.Nonlin.UnifIP IP α₂ cc clo Cup Ccs` | the paper's `IP` is Cauchy–Schwarz with a constant `Ccs`, and its linearity holds only on the regular class `RegQ`; `IsH4IP` was proved *false* for the concrete `IP` (design §0.5d) |
| 3 | `hField_lip : ∀ n τ, LipschitzOnWith ⟨K, hK⟩ …` (constant `K` uniform in `n`) | `K : ℕ → ℝ`, `hField_lip : ∀ n τ, LipschitzOnWith ⟨K n, …⟩ …` | `𝓛_Γ^T` is unbounded on `ℋ⁴`, so the projected field is *not* uniformly Lipschitz: `sup_n sup_ball ‖galField‖ = ∞` (design §1.2) |
| 4 | `Psi`, `hPsi : ∀ G τ, Law (F_*+G(τ)) (Ψ(G)(τ))` (arbitrary `G`) | the *canonical* operator `PsiCan Φ_* EllSol`, with the law required only on the Galerkin class | no solution exists for arbitrary `G`; N1 supplies a solution operator `EllSol` on `GalClass` (design §1.2, T10) |
| 5 | `hProfileLip : ∀ c, IsGalFam … → local Lipschitz bounds on the profiles` | `hProfileEquicont : ∀ c, IsGalFam … → locally uniform equicontinuity of the profiles` | a uniform *Lipschitz* modulus is false (an `ℋ⁴` ball contains `θ^s` profiles with `α/20 < s < 1`); the compactness extraction needs only equicontinuity, which is what the N4/N5 estimates actually give (design §1.2) |
| 6 | `DataAdm α g₀` (= `Coercivity.HkAdm α 4/5` + decay + vanishing) | `DataAdm α g₀ := LocData.DataAdm α g₀ ∧ L₁₂(g₀)(0) = 0 ∧ RegQ α 5 g₀` | `HkAdm` contains the analyticity class `SmoothNbhd`; N9's localised datum (and every PDE object) is not analytic (design §1.2) |

The bundle also carries the *structural* elliptic data of N1 (`Φs`, `EllSol`, `StarPkg`, `EllPkgG`)
which N5's `galerkin_bound` consumes, and the Galerkin basis is packaged in the corrected class
`Work.FTS.Nonlin.GalBasis` (orthonormality **plus** closure of the Galerkin span under `GalClass`),
replacing the three fields `hφ_orth`/`hφ_adm`/`hφ_vanish`.

Import order: `Work.FTS.Vocab` holds the frozen shared vocabulary (`RegQ`, `GalClass`, `UnifIP`,
`GalBasis`, …) and imports `Work.FTS.Galerkin.Defs`; the corrected bundle therefore lives here
(under `GalerkinFix/`), and `Work.FTS.Galerkin.DynInputs` is *this* structure.  Nothing in
`Work.FTS.Vocab` is redefined.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Vocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Galerkin

open Work.FTS.Nonlin (RegQ GalClass CoerAdm UnifIP GalBasis StarPkg EllPkgG PsiCan Xn)

set_option autoImplicit false

/-! ## The admissible data of the fixed theorem -/

/-- **The admissible data of the fixed Galerkin existence theorem** (design §1.2, row `DataAdm`):
the localised datum class `LocData.DataAdm` of the route, together with the vanishing of the zero
mode `L₁₂(·)(0)` and the interior regularity class `RegQ α 5` (which supplies the boundary traces at
order `5` and the honest `ℋ⁵`-membership needed by N5's a-priori estimate). -/
def DataAdm (α : ℝ) (g₀ : Fn) : Prop :=
  Work.FTS.LocData.DataAdm α g₀ ∧ Construction.L12 g₀ 0 = 0 ∧ RegQ α 5 g₀

theorem DataAdm.locData {α : ℝ} {g₀ : Fn} (h : DataAdm α g₀) :
    Work.FTS.LocData.DataAdm α g₀ := h.1

theorem DataAdm.l12 {α : ℝ} {g₀ : Fn} (h : DataAdm α g₀) : Construction.L12 g₀ 0 = 0 := h.2.1

theorem DataAdm.regQ {α : ℝ} {g₀ : Fn} (h : DataAdm α g₀) : RegQ α 5 g₀ := h.2.2

/-- **The corrected density of the Galerkin span**: density in the class `V₀ = {f ∈ ℋ⁴ : L₁₂(f)(0)
= 0}` of the interior-regular class (design §1.2, row `hφ_dense`).  Density relative to
`Coercivity.HkAdm`, which contains the analyticity hypothesis `SmoothNbhd`, is both hard and useless:
the flow does not preserve the zero modes of `HkAdm`, and the fundamental lemma is needed only on
`V₀`. -/
def DenseSpan (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) : Prop :=
  ∀ f : Fn, RegQ α 4 f → Construction.L12 f 0 = 0 → ∀ ε : ℝ, 0 < ε →
    ∃ (n : ℕ) (c : Fin n → ℝ), Spaces.HkNorm α 4 (fun z θ => f z θ - galFun φ c z θ) < ε

/-! ## The compactness inputs of the corrected bundle

The delivered bundle asked for a *uniform local Lipschitz bound* on the Gelarkin profiles
(`hProfileLip`).  That is not what the estimates give: the `ℋ⁴`-ball contains profiles `θ^s` which
are only `C^β` for `β < γ - 1 = α/10` (design §1.2).  The compactness extraction of
`Extraction.lean` uses a Lipschitz modulus only through the `ε`/`3` argument, and a *modulus of
continuity* suffices.  The corrected input is therefore uniform local **equicontinuity**, split into
its two sources, which are the two estimates the paper actually provides:

* in the space variables: the Hölder embedding `|g|_{C^β} ≤ C_β|g|_{ℋ²}` for `β < γ-1` (tex 1057,
  Corollary `Linfty`), i.e. a uniform `ℋ²`-bound gives a modulus in `(z,θ)` (`EquicontSpace`);
* in the fake time: the estimate `|∂_τg|_{ℋ³} ≤ Cα² exp(-cτ)` (tex 1580) together with the pointwise
  bound of `Linf_H2` (`EquicontTau`);

see `Submission/Work/FTS/GalerkinFix/Equicont.lean` for the chapter that combines them. -/

/-- **Uniform local boundedness** of a sequence of profiles on the fake-time slab (N5 through the
paper's `Linf_H2`: a uniform `ℋ⁴`-bound gives pointwise bounds on compact subsets). -/
def ProfileBdd (G : ℕ → (ℝ × ℝ × ℝ) → ℝ) : Prop :=
  ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K → K ⊆ Slab →
    ∃ C : ℝ, ∀ n : ℕ, ∀ p ∈ K, |G n p| ≤ C

/-- **Uniform local equicontinuity** of a sequence of profiles on the fake-time slab — the corrected
compactness input replacing `hProfileLip`, obtained from `EquicontSpace` and `EquicontTau` by
`Work.FTS.GalerkinFix.profileEquicont_of_parts` and `…_of_box`. -/
def ProfileEquicont (G : ℕ → (ℝ × ℝ × ℝ) → ℝ) : Prop :=
  ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K → K ⊆ Slab → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ Slab, dist p q ≤ δ → |G n p - G n q| ≤ ε

/-- The rectangle `[0,Z] × [0,π/2] × [0,T]` of the self-similar slab. -/
def box (Z T : ℝ) : Set (ℝ × ℝ × ℝ) := Set.Icc 0 Z ×ˢ (Set.Icc 0 (π / 2) ×ˢ Set.Icc 0 T)

theorem mem_box {Z T : ℝ} {p : ℝ × ℝ × ℝ} :
    p ∈ box Z T ↔ p.1 ∈ Set.Icc 0 Z ∧ p.2.1 ∈ Set.Icc 0 (π / 2) ∧ p.2.2 ∈ Set.Icc 0 T :=
  Iff.rfl

theorem box_subset_slab {Z T : ℝ} (hZ : 0 ≤ Z) : box Z T ⊆ Slab := by
  intro p hp
  rw [mem_box] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  exact ⟨(Set.mem_Icc.mp h1).1, Set.mem_Icc.mp h2, (Set.mem_Icc.mp h3).1⟩

/-- **Spatial equicontinuity of a sequence of profiles**, with a modulus on every rectangle of the
slab (uniform in the truncation `n` and in the fake time `τ`).  This is the `(z,θ)`-half of the
corrected compactness input; it is supplied by a uniform Hölder modulus of the profiles (the scalar
estimate `Linf_H2`, tex 1057), which in *this* vocabulary must come with the continuity of the
profiles up to the angular boundary: `SmoothQuad` + `VanishTheta` alone do not force the one-sided
limits at `θ = 0, π/2` (see `Submission/Work/FTS/GalerkinFix/README.md` §2.1 and
`Work.FTS.GalerkinFix.LinfQ.holder_modulus_of_HkNorm_two_continuous`).  The reduction from such a
modulus to this statement is `Work.FTS.GalerkinFix.equicontSpace_of_holderBound`. -/
def EquicontSpace (G : ℕ → (ℝ × ℝ × ℝ) → ℝ) : Prop :=
  ∀ Z T : ℝ, 0 ≤ Z → 0 ≤ T → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ,
    ∀ τ ∈ Set.Icc 0 T, ∀ z ∈ Set.Icc 0 Z, ∀ θ ∈ Set.Icc 0 (π / 2),
      ∀ z' ∈ Set.Icc 0 Z, ∀ θ' ∈ Set.Icc 0 (π / 2),
        |z - z'| ≤ δ → |θ - θ'| ≤ δ → |G n (z, θ, τ) - G n (z', θ', τ)| ≤ ε

/-- **Equicontinuity of a sequence of profiles in the fake time**, with a modulus on every rectangle
of the slab (uniform in the truncation `n`).  This is the `τ`-half of the corrected compactness
input; it is supplied by the paper's estimate `|∂_τg|_{ℋ³} ≤ Cα² exp(-cτ)` through
`Work.FTS.GalerkinFix.equicontTau_of_galFam_fieldBound`. -/
def EquicontTau (G : ℕ → (ℝ × ℝ × ℝ) → ℝ) : Prop :=
  ∀ Z T : ℝ, 0 ≤ Z → 0 ≤ T → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ,
    ∀ z ∈ Set.Icc 0 Z, ∀ θ ∈ Set.Icc 0 (π / 2),
      ∀ t ∈ Set.Icc 0 T, ∀ s ∈ Set.Icc 0 T,
        |t - s| ≤ δ → |G n (z, θ, t) - G n (z, θ, s)| ≤ ε

/-- **Joint equicontinuity on every rectangle of the slab** — the immediate combination of the two
one-directional moduli. -/
def ProfileEquicontBox (G : ℕ → (ℝ × ℝ × ℝ) → ℝ) : Prop :=
  ∀ Z T : ℝ, 0 ≤ Z → 0 ≤ T → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ,
    ∀ p ∈ box Z T, ∀ q ∈ box Z T, dist p q ≤ δ → |G n p - G n q| ≤ ε

/-- The profile family of a Galerkin coefficient family, as a function on the fake-time slab. -/
def profileFam (φ : ℕ → Fn) (c : ∀ n : ℕ, ℝ → Fin n → ℝ) : ℕ → (ℝ × ℝ × ℝ) → ℝ :=
  fun n p => prof φ c n p

@[simp] theorem profileFam_apply (φ : ℕ → Fn) (c : ∀ n : ℕ, ℝ → Fin n → ℝ) (n : ℕ)
    (p : ℝ × ℝ × ℝ) : profileFam φ c n p = prof φ c n p := rfl

/-! ## The corrected a-priori bundle -/

/-- **The corrected a-priori input bundle of the Galerkin existence theorem** (design §1.2–1.3).

Every field is a statement *about* the objects of the argument; there is no existence assertion
among them — existence of a solution of the dynamic modulated equation is what
`Work.FTS.Galerkin.exists_dynGSol_of_ode` proves from this bundle.

* `IP`, `α₂`, `cc`, `clo`, `Cup`, `Ccs`, `hIP` (N2): the `ℋ⁴` inner product with the *uniform*
  coercivity/comparability/Cauchy–Schwarz constants of `Work.FTS.Nonlin.UnifIP`.  Its linearity is
  restricted to the regular class `RegQ α 4`.
* `φ`, `hφ` (N6 step 2): the Galerkin basis, as `GalBasis α IP φ` — `IP`-orthonormal and with every
  Galerkin combination in `GalClass α`.  The old fields `hφ_orth`/`hφ_adm`/`hφ_vanish` are replaced
  by this single class (they are its consequences: `Work.FTS.GalerkinFix.galBasis_orth`,
  `…_vanish`).
* `hφ_dense` (N6 step 2): density of the span in `V₀` (`DenseSpan`).
* `Φs`, `Cs`, `hΦs` (N3): the stream function of `F_*` and its `𝒲^{l,∞}` package (`StarPkg`).
* `EllSol`, `Ce`, `hEllSol` (N1): the *canonical* stream-function operator, defined on `GalClass`
  with the elliptic package `EllPkgG` (source `g`, stream function `EllSol g`).
* `hPsi` (N1): the stream function of the profile `F_* + G(τ)` is `PsiCan Φs EllSol G` and solves
  the elliptic law `Law`, for every family whose slices are in `GalClass`.
* `R`, `hR` (N5): the radius of the a-priori ball.
* `L : ℕ → ℝ`, `K : ℕ → ℝ`, `hField_lip`, `hField_bound`, `hField_cont` (N4): the projected vector
  field is Lipschitz/bounded/`τ`-continuous on the ball of radius `2R` of `Fin n → ℝ`, **with
  constants depending on the truncation** `n` (they cannot be uniform: `𝓛_Γ^T` is unbounded).
* `hInit`, `hCoeffBound` (N5): the projected datum and every Galerkin solution stay in the ball.
* `hProfileBdd` (N5): uniform local bounds on the profiles.
* `hProfileEquicont` (N4+N5): uniform local **equicontinuity** of the profiles — the compactness
  input (replaces `hProfileLip`).
* `hRegLimit` (N5/N7): the regularity package of the limit.
* `hDataLimit` (N6 step 2): the `τ = 0` slice of the limit is the datum.
* `hPsiLim` (N1): the stream functions have a locally uniform limit.
* `hGalWeak` (N1+N4): the tested equations and the elliptic law pass to the limit.
* `hDetermines` (N6 step 6): the fundamental lemma for the dense Galerkin span.
* `hLimBound` (N5): the a-priori `ℋ⁴`-bound `C₀α²` for the **limit** of the Galerkin family
  (replaces `hApriori`, which asked the same for *every* solution of the dynamic equation). -/
structure DynInputs (Law : Fn → Fn → Prop) (α : ℝ) (g₀ : Fn) (C₀ : ℝ) where
  /-- the `ℋ⁴` inner product (N2). -/
  IP : ℝ → Fn → Fn → ℝ
  /-- the range of validity of the uniform inner-product bounds (N2). -/
  α₂ : ℝ
  /-- the coercivity constant of `𝓛_Γ^T` (N2). -/
  cc : ℝ
  /-- the lower comparability constant of `IP` (N2). -/
  clo : ℝ
  /-- the upper comparability constant of `IP` (N2). -/
  Cup : ℝ
  /-- the Cauchy–Schwarz constant of `IP` (N2). -/
  Ccs : ℝ
  /-- **the uniform inner-product structure** (N2). -/
  hIP : UnifIP IP α₂ cc clo Cup Ccs
  /-- the Galerkin test sequence (N6 step 2). -/
  φ : ℕ → Fn
  /-- **the Galerkin basis class**: `IP`-orthonormal, with every Galerkin combination in
  `GalClass` (N6 step 2, corrected). -/
  hφ : GalBasis α IP φ
  /-- the span of the test sequence is dense in `V₀` (N6 step 2, corrected). -/
  hφ_dense : DenseSpan α IP φ
  /-- the stream function of `F_*` (N3). -/
  Φs : Fn
  /-- the canonical stream-function operator for the perturbation (N1). -/
  EllSol : Fn → Fn
  /-- the `𝒲^{l,∞}` constant of the profile (N3). -/
  Cs : ℝ
  /-- the elliptic constant of the perturbation's stream function (N1). -/
  Ce : ℝ
  /-- the stream function of `F_*` and its `𝒲^{l,∞}` package (N3). -/
  hΦs : StarPkg α Cs Φs
  /-- the elliptic package of the perturbation's stream function, on the Galerkin class (N1). -/
  hEllSol : ∀ g : Fn, GalClass α g → EllPkgG α Ce g (EllSol g)
  /-- the stream function of `F_* + G(τ)` is `PsiCan Φs EllSol G`, and it satisfies the elliptic law
  at every `τ ≥ 0` for families whose slices lie in `GalClass` (N1). -/
  hPsi : ∀ G : Fam, (∀ τ : ℝ, 0 ≤ τ → GalClass α (slice G τ)) → ∀ τ : ℝ, 0 ≤ τ →
    Law (Construction.Ftau α G τ) (slice (PsiCan Φs EllSol G) τ)
  /-- the radius of the a-priori ball for the coefficients. -/
  R : ℝ
  hR : 0 < R
  /-- a bound for the projected vector field on the ball of radius `2R`, depending on the
  truncation (N4). -/
  L : ℕ → ℝ
  hL : ∀ n : ℕ, 0 < L n
  /-- a Lipschitz constant for the projected vector field on the ball of radius `2R`, depending on
  the truncation (N4). -/
  K : ℕ → ℝ
  hK : ∀ n : ℕ, 0 ≤ K n
  /-- the projected vector field is Lipschitz in the coefficients, with truncation-dependent
  constant (N4). -/
  hField_lip : ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ →
    LipschitzOnWith ⟨K n, hK n⟩ (galField α (IP α) φ n (PsiCan Φs EllSol) τ)
      (Metric.closedBall 0 (2 * R))
  /-- the projected vector field is bounded on the ball of radius `2R`, with truncation-dependent
  constant (N4). -/
  hField_bound : ∀ (n : ℕ) (τ : ℝ) (c : Fin n → ℝ), 0 ≤ τ →
    c ∈ Metric.closedBall 0 (2 * R) → ‖galField α (IP α) φ n (PsiCan Φs EllSol) τ c‖ ≤ L n
  /-- the projected vector field is continuous in fake time (N1 + N4). -/
  hField_cont : ∀ (n : ℕ) (c : Fin n → ℝ), c ∈ Metric.closedBall 0 (2 * R) →
    ContinuousOn (fun τ => galField α (IP α) φ n (PsiCan Φs EllSol) τ c) (Set.Ici 0)
  /-- the projected datum lies in the a-priori ball, in the energy (`ℓ²`) form. -/
  hInit : ∀ n : ℕ, ∑ k : Fin n, (coeffOf (IP α) g₀ φ n k) ^ 2 ≤ R ^ 2
  /-- **the a-priori estimate**: the coefficients of every Galerkin solution stay in the ball
  (N5, using the exact energy identity of step 4). -/
  hCoeffBound : ∀ (n : ℕ) (T : ℝ), 0 ≤ T → ∀ c : ℝ → Fin n → ℝ,
    IsSolOn (galField α (IP α) φ n (PsiCan Φs EllSol)) (coeffOf (IP α) g₀ φ n) T c →
    ∀ τ ∈ Set.Icc 0 T, ∑ k : Fin n, (c τ k) ^ 2 ≤ R ^ 2
  /-- **uniform local bounds on the Galerkin profiles** (N5 through the paper's `Linf_H2`). -/
  hProfileBdd : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c →
    ProfileBdd (profileFam φ c)
  /-- **uniform spatial equicontinuity of the Galerkin profiles** (N4 + N5): the `(z,θ)`-half of the
  corrected compactness input, supplied by the paper's Hölder embedding
  `|g|_{C^β} ≤ C_β|g|_{ℋ²}` (`β < γ-1`, tex 1057) from a uniform `ℋ²`-bound on the profiles. -/
  hProfileSpace : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c →
    EquicontSpace (profileFam φ c)
  /-- **uniform equicontinuity of the Galerkin profiles in the fake time** (N4 + N5): the
  `τ`-half of the corrected compactness input, supplied by the paper's estimate
  `|∂_τg|_{ℋ³} ≤ Cα² exp(-cτ)` (tex 1580) through
  `Work.FTS.GalerkinFix.equicontTau_of_galFam_fieldBound`.  These two fields replace the delivered
  `hProfileLip`. -/
  hProfileTau : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c →
    EquicontTau (profileFam φ c)
  /-- **the regularity package of the limit** (N5/N7). -/
  hRegLimit : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g → RegPkg α g
  /-- **the datum is the limit of the projected data** (N6 step 2). -/
  hDataLimit : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g → ∀ z θ, g z θ 0 = g₀ z θ
  /-- **the stream functions have a locally uniform limit** (N1). -/
  hPsiLim : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    ∃ Φ : Fam, ConvLocUnif (fun n => PsiCan Φs EllSol (galFam φ (ψ n) (c (ψ n)))) Φ
  /-- **the tested equations pass to the limit** (N1 + N4). -/
  hGalWeak : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g Φ : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    ConvLocUnif (fun n => PsiCan Φs EllSol (galFam φ (ψ n) (c (ψ n)))) Φ →
    IsDynWeakOn α (IP α) φ g Φ ∧ (∀ τ : ℝ, 0 ≤ τ → Law (Construction.Ftau α g τ) (slice Φ τ))
  /-- **the fundamental lemma of the calculus of variations** for the dense Galerkin span
  (N6 step 6). -/
  hDetermines : WeakDetermines α (IP α) φ
  /-- **the a-priori estimate in limit form** (N5): the limit of the Galerkin family obeys the
  uniform `ℋ⁴`-bound `C₀α²`.  This replaces the delivered field `hApriori`. -/
  hLimBound : ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → ∀ (ψ : ℕ → ℕ) (g : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    ∀ τ : ℝ, 0 ≤ τ → Spaces.HkNorm α 4 (slice g τ) ≤ C₀ * α ^ 2

/-- The stream-function assignment of the bundle: the canonical operator `PsiCan Φs EllSol` of
N1, i.e. `Ψ(F_* + g) = Φ_* + EllSol(g)`. -/
def DynInputs.Psi {Law : Fn → Fn → Prop} {α : ℝ} {g₀ : Fn} {C₀ : ℝ}
    (hin : DynInputs Law α g₀ C₀) : Fam → Fam :=
  PsiCan hin.Φs hin.EllSol

theorem DynInputs.Psi_eq {Law : Fn → Fn → Prop} {α : ℝ} {g₀ : Fn} {C₀ : ℝ}
    (hin : DynInputs Law α g₀ C₀) :
    hin.Psi = PsiCan hin.Φs hin.EllSol := rfl

@[simp] theorem DynInputs.Psi_apply {Law : Fn → Fn → Prop} {α : ℝ} {g₀ : Fn} {C₀ : ℝ}
    (hin : DynInputs Law α g₀ C₀) (G : Fam) (z θ τ : ℝ) :
    hin.Psi G z θ τ = hin.Φs z θ + hin.EllSol (slice G τ) z θ := rfl

end Work.FTS.Galerkin
