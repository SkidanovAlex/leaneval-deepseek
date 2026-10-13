/-
  annals_wilkies_conjecture : areas C (Wilkie complement) and G (BNZ algebraic lemma)
  sub-area statements. curric-46 C/G design, 2026-10-08. Design text: cbc/wilkies_design.md
  plus the C/G report.

  Type-check on 18.221 from the workspace dir (it imports the frozen vocabulary):
    systemd-run --user --scope -q -p MemoryMax=12G -p CPUQuota=200% timeout 1200 \
      lake env lean /abs/path/wilkies_CG_stmts.lean
  Every `sorry` here is a dispatchable hole. The `*_wiring` theorems are fully proved from
  the holes.

  Interface change proposed for C: `C_wilkie_complement` additionally takes
    hUF : UnifFiniteRExp     (proved by the new hole E0b_unif_finite, inside E)
    hPB : PolyBoundedRExp    (new research area C4a)
  The frozen TOP wiring changes only by passing these two in.
-/
import Submission.Work.Wilkies.Defs
import Mathlib.ModelTheory.ElementarySubstructures

set_option autoImplicit false
noncomputable section
open Classical
namespace WilkiesDesign.CG
open WilkiesConjecture WilkiesDesign FirstOrder Language

/-! ##################################################################
    # AREA C : Wilkie (model completeness of ℝ_exp) via van den Dries–Macintyre–Marker
    ################################################################## -/

/-! ### C.0 Languages and theories (all reals named as constants) -/

inductive rexpFunc : ℕ → Type
  | rexp : rexpFunc 1

/-- One unary symbol for the restricted exponential. -/
def rexpL : Language where
  Functions := rexpFunc
  Relations _ := Empty
  deriving Language.IsAlgebraic

instance : rexpL.Structure ℝ where
  funMap {n} f := match n, f with
    | 1, .rexp => fun x => rexp (x 0)

/-- `L_rexp = ring ⊕ rexp`. -/
abbrev LR : Language := Language.ring.sum rexpL
/-- `L_rexp` with a constant for every real. -/
abbrev LRc : Language := LR[[ℝ]]
/-- `L_exp` with a constant for every real. -/
abbrev LEc : Language := expRing[[ℝ]]

/-- `T_r = Th(ℝ_rexp, (r)_{r ∈ ℝ})`. Its models are exactly the elementary extensions of ℝ_rexp. -/
def TR : LRc.Theory := LRc.completeTheory ℝ
/-- `T_e = Th(ℝ_exp, (r)_{r ∈ ℝ})`. -/
def TE : LEc.Theory := LEc.completeTheory ℝ

/-- Model completeness (Robinson): every embedding between models is elementary. -/
def ModelComplete {L : Language.{0, 0}} (T : L.Theory) : Prop :=
  ∀ (M N : Type) [L.Structure M] [L.Structure N] [M ⊨ T] [N ⊨ T] (f : M ↪[L] N)
    {n : ℕ} (φ : L.Formula (Fin n)) (x : Fin n → M), φ.Realize (f ∘ x) ↔ φ.Realize x

/-! ### C.1 Hypotheses supplied from outside C -/

/-- Uniform finiteness for rexp-existential families: one bound for every fibre.
Area E proves it (E0b) from `SOMin.comps`, via fibres of `Ω`-sets. -/
def UnifFiniteRExp : Prop :=
  ∀ (k : ℕ) (Y : Set (Fin (k + 1) → ℝ)), RExpExist Y →
    ∃ N : ℕ, ∀ c : Fin k → ℝ, ∃ s : Finset (Set ℝ), s.card ≤ N ∧
      (∀ I ∈ s, IsPreconnected I) ∧ {t : ℝ | Fin.cons t c ∈ Y} = ⋃₀ (s : Set (Set ℝ))

/-- Uniform polynomial boundedness with rational exponents (Puiseux at infinity) for
rexp-existential families of functions `x ↦ y` with parameter `c`. One FINITE set of
exponents serves the whole family, so the statement is a first-order schema and transfers
to every model of `TR`. This is the analytic heart of C. -/
def PolyBoundedRExp : Prop :=
  ∀ (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)), RExpExist Y →
    (∀ (c : Fin k → ℝ) (x y y' : ℝ), Fin.cons x (Fin.cons y c) ∈ Y →
        Fin.cons x (Fin.cons y' c) ∈ Y → y = y') →
    ∃ Qs : Finset ℚ, ∀ c : Fin k → ℝ,
      (∃ R : ℝ, ∀ x y : ℝ, R ≤ x → Fin.cons x (Fin.cons y c) ∈ Y → y = 0) ∨
      ∃ q ∈ Qs, ∃ a : ℝ, a ≠ 0 ∧ ∀ ε > (0 : ℝ), ∃ R : ℝ, ∀ x y : ℝ, R ≤ x →
        Fin.cons x (Fin.cons y c) ∈ Y → |y / x ^ (q : ℝ) - a| < ε

/-! ### C.2 Valuation-theoretic vocabulary for models of `TR` -/

/-- `v(x) = 0` for the natural (archimedean) valuation over ℝ. -/
def IsUnitVal {M : Type} [Field M] [LinearOrder M] (x : M) : Prop :=
  ∃ N : ℕ, ((N : M) + 1)⁻¹ ≤ |x| ∧ |x| ≤ (N : M) + 1

/-- Every model of `TR` is o-minimal (definable subsets of the line, parameters from `M`). -/
def OMinModels : Prop :=
  ∀ (M : Type) [Field M] [LinearOrder M] [IsStrictOrderedRing M] [Ring.CompatibleRing M]
    [rexpL.Structure M] [(constantsOn ℝ).Structure M] [M ⊨ TR] (X : Set (Fin 1 → M)),
    (Set.univ : Set M).Definable LRc X →
    ∃ s : Finset (Set M), (∀ I ∈ s, I.OrdConnected) ∧ X = {x | x 0 ∈ ⋃₀ (s : Set (Set M))}

/-- Wilkie's relativised valuation inequality for `TR`, with residue rank 0 (every model of
`TR` has residue field ℝ): if `M = dcl(S ∪ {a₁..a_k})` contains `b₁..b_m` whose values are
ℚ-independent modulo `v(S^×)`, then `m ≤ k`. Integer exponents suffice because `v(S^×)` is
divisible. -/
def ValIneq : Prop :=
  ∀ (M : Type) [Field M] [LinearOrder M] [IsStrictOrderedRing M] [Ring.CompatibleRing M]
    [rexpL.Structure M] [(constantsOn ℝ).Structure M] [M ⊨ TR]
    (S : LRc.ElementarySubstructure M) {k m : ℕ} (a : Fin k → M) (b : Fin m → M),
    (∀ j, b j ≠ 0) →
    (∀ j, ((S : Set M) ∪ Set.range a).Definable LRc {fun _ : Fin 1 => b j}) →
    (∀ q : Fin m → ℤ, (∃ c ∈ (S : Set M), c ≠ 0 ∧ IsUnitVal (c * ∏ j, b j ^ q j)) → q = 0) →
    m ≤ k

/-! ### C.3 Holes -/

/-- **E0b (inside E, mechanical given E's Ω):** rexp-existential families have uniformly
finitely many fibre components. -/
theorem E0b_unif_finite : UnifFiniteRExp := by
  sorry

/-- **C0 (syntax, mechanical; shares B's flattening code).** With E0, every `LRc`-definable
set of ℝ (any formula, real constants) is `RExpExist`. -/
theorem C0_rexp_syntax (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    {n : ℕ} (X : Set (Fin n → ℝ)) (h : (∅ : Set ℝ).Definable LRc X) : RExpExist X := by
  sorry

/-- **C1 (mechanical given C0):** `TR` is model complete. -/
theorem C1_TR_modelComplete
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ) :
    ModelComplete TR := by
  sorry

/-- **C2 (o-minimal model theory):** uniform finiteness in ℝ transfers to every model. -/
theorem C2_models_ominimal
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (hUF : UnifFiniteRExp) : OMinModels := by
  sorry

/-- **C4a (RESEARCH, analytic):** ℝ_rexp is polynomially bounded with exponents in ℚ,
uniformly in parameters. -/
theorem C4a_rexp_polyBounded
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (hUF : UnifFiniteRExp) : PolyBoundedRExp := by
  sorry

/-- **C4 (RESEARCH, o-minimal valuation theory):** Wilkie's valuation inequality for `TR`. -/
theorem C4_valuation_inequality
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (hOM : OMinModels) (hPB : PolyBoundedRExp) : ValIneq := by
  sorry

/-- **C5 (vdDMM §4 + (4.10), research-mechanical):** the Ressayre/vdDMM embedding lemmas
4.2–4.4 give model completeness of `T_e`. -/
theorem C5_TE_modelComplete (hMCr : ModelComplete TR) (hOM : OMinModels)
    (hVI : ValIneq) : ModelComplete TE := by
  sorry

/-- **C6 (compactness + syntax, mechanical):** model completeness of `T_e` gives the
complement of an `ExpExist` set as an `ExpExist` set. -/
theorem C6_compl_of_modelComplete (hMC : ModelComplete TE) {n : ℕ}
    (X : Set (Fin n → ℝ)) (h : ExpExist X) : ExpExist Xᶜ := by
  sorry

/-- **C wiring (proved):** the proposed new signature of `C_wilkie_complement`. -/
theorem C_wilkie_complement_wiring
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (hUF : UnifFiniteRExp) (hPB : PolyBoundedRExp)
    {n : ℕ} (X : Set (Fin n → ℝ)) (h : ExpExist X) : ExpExist Xᶜ :=
  have hOM := C2_models_ominimal hR hUF
  C6_compl_of_modelComplete
    (C5_TE_modelComplete (C1_TR_modelComplete hR) hOM (C4_valuation_inequality hR hOM hPB))
    X h

/-! ##################################################################
    # AREA G : BNZ algebraic lemma (Lemma 3 / F-lem), over an abstract SOMin
    ################################################################## -/

/-! ### G.0 The Ω-formula calculus (format depends on the shape only; degrees add up) -/

/-- Shapes of first-order formulas over `Ω`. The atoms are a polynomial equation, or
membership of a coordinate substitution `x ∘ ι` in an `Ω`-set. `ex` quantifies the last
variable. -/
inductive OShape : ℕ → Type
  | poly (n : ℕ) : OShape n
  | mem (n m : ℕ) (ι : Fin m → Fin n) : OShape n
  | neg {n : ℕ} : OShape n → OShape n
  | and {n : ℕ} : OShape n → OShape n → OShape n
  | or {n : ℕ} : OShape n → OShape n → OShape n
  | ex {n : ℕ} : OShape (n + 1) → OShape n

/-- Atom data. A `mem` atom carries the set and its declared degree. -/
def OShape.Data : {n : ℕ} → OShape n → Type
  | _, .poly n => MvPolynomial (Fin n) ℝ
  | _, .mem _ m _ => Set (Fin m → ℝ) × ℕ
  | _, .neg s => s.Data
  | _, .and s t => s.Data × t.Data
  | _, .or s t => s.Data × t.Data
  | _, .ex s => s.Data

def OShape.realize : {n : ℕ} → (s : OShape n) → s.Data → Set (Fin n → ℝ)
  | _, .poly _, P => {x | MvPolynomial.eval x P = 0}
  | _, .mem _ _ ι, d => {x | x ∘ ι ∈ d.1}
  | _, .neg s, d => (s.realize d)ᶜ
  | _, .and s t, d => s.realize d.1 ∩ t.realize d.2
  | _, .or s t, d => s.realize d.1 ∪ t.realize d.2
  | _, .ex s, d => projLast (s.realize d)

/-- Degree bookkeeping. A substitution atom costs `+2`, for the equation `Σ (w_j - x_{ι j})² = 0`. -/
def OShape.deg : {n : ℕ} → (s : OShape n) → s.Data → ℕ
  | _, .poly _, P => P.totalDegree
  | _, .mem _ _ _, d => d.2 + 2
  | _, .neg s, d => s.deg d
  | _, .and s t, d => s.deg d.1 + t.deg d.2
  | _, .or s t, d => s.deg d.1 + t.deg d.2
  | _, .ex s, d => s.deg d

def OShape.Good (S : SOMin) (F : ℕ) : {n : ℕ} → (s : OShape n) → s.Data → Prop
  | _, .poly _, _ => True
  | _, .mem _ m _, d => d.1 ∈ S.Ω F d.2 m
  | _, .neg s, d => s.Good S F d
  | _, .and s t, d => s.Good S F d.1 ∧ t.Good S F d.2
  | _, .or s t, d => s.Good S F d.1 ∧ t.Good S F d.2
  | _, .ex s, d => s.Good S F d

/-- **G0 (mechanical, shared with H).** -/
theorem G0_calculus (S : SOMin) {n : ℕ} (s : OShape n) (F : ℕ) :
    ∃ a : ℕ, ∀ d : s.Data, s.Good S F d → s.realize d ∈ S.Ω a (s.deg d) n := by
  sorry

/-! ### G.1 Effective o-minimal geometry from the axioms (shared with H) -/

/-- **G1a: definable choice with sharp bounds** (BNZ §2.3; uses SharpCD). -/
theorem G1_choice (S : SOMin) (hcd : S.SharpCD) (F p n : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (X : Set (Fin (p + n) → ℝ)),
      X ∈ S.Ω F D (p + n) →
      ∃ f : (Fin p → ℝ) → (Fin n → ℝ),
        (∀ l : Fin p → ℝ, (∃ y, Fin.append l y ∈ X) → Fin.append l (f l) ∈ X) ∧
        {z : Fin (p + n) → ℝ | ∀ j : Fin n,
            z (Fin.natAdd p j) = f (fun i => z (Fin.castAdd n i)) j} ∈ S.Ω a (b.eval D) (p + n) := by
  sorry

/-- **G1b: generic smoothness.** A definable function is `C^k` off a set with empty interior. -/
theorem G1_generic_smooth (S : SOMin) (hcd : S.SharpCD) {n F D : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : graphOf f ∈ S.Ω F D (n + 1)) (k : ℕ) :
    interior {x | ¬ ContDiffAt ℝ k f x} = ∅ := by
  sorry

/-! ### G.2 The jet ("T") norm -/

/-- `‖f‖_{T,r}` at a point, with operator norms: `Σ_{k ≤ r} ‖D^k f(x)‖ / k!`. -/
def tnorm {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℕ) (f : E → ℝ) (x : E) : ℝ :=
  ∑ k ∈ Finset.range (r + 1), ‖iteratedFDeriv ℝ k f x‖ / (k.factorial : ℝ)

/-- **G2a: submultiplicativity** (BNZ Lemma 4.2(i)). -/
theorem G2_tnorm_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℕ)
    (f g : E → ℝ) (x : E) (hf : ContDiffAt ℝ r f x) (hg : ContDiffAt ℝ r g x) :
    tnorm r (f * g) x ≤ tnorm r f x * tnorm r g x := by
  sorry

/-- **G2b: subcompositionality** (BNZ Lemma 4.2(ii); Faà di Bruno + exponential formula). -/
theorem G2_tnorm_comp {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ} (r : ℕ)
    (F : E → (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ) (x : E)
    (hF : ContDiffAt ℝ r F x) (hg : ContDiffAt ℝ r g (F x))
    (h1 : ∑ k ∈ Finset.Ico 1 (r + 1), ‖iteratedFDeriv ℝ k F x‖ / (k.factorial : ℝ) ≤ 1) :
    tnorm r (g ∘ F) x ≤ tnorm r g (F x) := by
  sorry

/-! ### G.3 One-dimensional lemmas -/

/-- **G3a: BNZ Lemma 5.4 (discrete C^r).** -/
theorem G3_discrete_Cr (r : ℕ) (f : ℝ → ℝ) (hf : ContDiffOn ℝ (r + 1) f (Set.Ioo 0 1))
    (hI : ∀ x ∈ Set.Ioo (0 : ℝ) 1, f x ∈ Set.Ioo (0 : ℝ) 1)
    (hsign : ∀ j ≤ r + 1, (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ iteratedDerivWithin j f (Set.Ioo 0 1) x) ∨
      (∀ x ∈ Set.Ioo (0 : ℝ) 1, iteratedDerivWithin j f (Set.Ioo 0 1) x ≤ 0))
    (M : ℝ) (hM : 1 < M) :
    ∀ j ≤ r, ∀ x ∈ Set.Ioo (0 : ℝ) 1, (j : ℝ) / M < x → x < 1 - j / M →
      |iteratedDerivWithin j f (Set.Ioo 0 1) x| < M ^ j := by
  sorry

/-- **G3b: the Whitney-type affine cover of `[ε, 1-ε]`.** Each interval `[u,v]` has length at
most `dist([u,v], {0,1})/(r+1)`, so G3a applies to every affine chart of it. -/
theorem G3_affine_cover (r : ℕ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ s : Finset (ℝ × ℝ), (s.card : ℝ) ≤ 8 * (r + 1) * (-Real.log ε + 2) ∧
      (∀ p ∈ s, 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1 ∧
        (p.2 - p.1) * (r + 1) ≤ min p.1 (1 - p.2)) ∧
      Set.Icc ε (1 - ε) ⊆ ⋃ p ∈ s, Set.Icc p.1 p.2 := by
  sorry

/-! ### G.4 Families and the F-lemma (BNZ Lemma 5.1) -/

/-- Graph of a family `F : Λ × ℝⁿ → ℝ` inside `ℝ^{p+n+1}`. -/
def famGraph {p n : ℕ} (F : (Fin p → ℝ) → (Fin n → ℝ) → ℝ) : Set (Fin (p + n + 1) → ℝ) :=
  graphOf (fun z : Fin (p + n) → ℝ =>
    F (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd p j)))

/-- BNZ Lemma 5.1 (F-lem) with operator norms. Format and degree of the charts are
independent of `k` and `ε`. -/
def FLem (S : SOMin) (p n : ℕ) : Prop :=
  ∀ F0 : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
    ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
    ∀ (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → (Fin n → ℝ) → ℝ),
      (∀ i, famGraph (F i) ∈ S.Ω F0 D (p + n + 1)) →
      (∀ i, ∀ l ∈ Λ, ∀ x ∈ openCube n, F i l x ∈ Set.Ioo (0 : ℝ) 1) →
      ∃ Φ : Finset (Fin n → (Fin p → ℝ) → (Fin n → ℝ) → ℝ),
        (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
        (∀ φ ∈ Φ, (∀ j, famGraph (φ j) ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + n + 1)) ∧
          ∀ l ∈ Λ, (∀ t ∈ openCube n, (fun j => φ j l t) ∈ openCube n) ∧
            ∀ i, ContDiffOn ℝ r (fun t => F i l (fun j => φ j l t)) (openCube n) ∧
              ∀ m ≤ r, ∀ t ∈ openCube n,
                ‖iteratedFDeriv ℝ m (fun t => F i l (fun j => φ j l t)) t‖ ≤ 1) ∧
        ∀ l ∈ Λ, ∀ x ∈ openCube n, ∃ φ ∈ Φ, ∃ t ∈ openCube n,
          ∀ i, |F i l (fun j => φ j l t) - F i l x| < ε

/-- BNZ Cor 5.5 (F1-affine): affine charts in the single variable, an ε-cover of the DOMAIN
(not of the image), and `C^r` norms `≤ 1`. -/
def F1Affine (S : SOMin) (p : ℕ) : Prop :=
  ∀ F0 : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
    ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
    ∀ (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ),
      (∀ i, famGraph (F i) ∈ S.Ω F0 D (p + 1 + 1)) →
      (∀ i, ∀ l ∈ Λ, ∀ x ∈ openCube 1, F i l x ∈ Set.Ioo (0 : ℝ) 1) →
      ∃ Φ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ)),   -- φ_l(t) = α l + β l * t
        (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
        (∀ αβ ∈ Φ, graphOf αβ.1 ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) ∧
          graphOf αβ.2 ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) ∧
          ∀ l ∈ Λ, 0 < αβ.2 l ∧ 0 ≤ αβ.1 l ∧ αβ.1 l + αβ.2 l ≤ 1 ∧
            ∀ i, ContDiffOn ℝ r (fun t : Fin 1 → ℝ => F i l (fun _ => αβ.1 l + αβ.2 l * t 0))
                (openCube 1) ∧
              ∀ m ≤ r, ∀ t ∈ openCube 1, ‖iteratedFDeriv ℝ m
                (fun t : Fin 1 → ℝ => F i l (fun _ => αβ.1 l + αβ.2 l * t 0)) t‖ ≤ 1) ∧
        ∀ l ∈ Λ, ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∃ αβ ∈ Φ, ∃ t ∈ Set.Ioo (0 : ℝ) 1,
          |αβ.1 l + αβ.2 l * t - x| < ε

/-- **G4z (trivial):** `n = 0`. -/
theorem G4_zero (S : SOMin) (p : ℕ) : FLem S p 0 := by
  sorry

/-- **G4a: the 1-D base** (BNZ §5.1 = Lemma 5.3 full-C1 + G3a + G3b). It also yields F1Affine. -/
theorem G4_base (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (p : ℕ) :
    FLem S p 1 ∧ F1Affine S p := by
  sorry

/-- **G4b: BNZ Lemma 5.6 / Binyamini–Novikov 'Yomdin–Gromov revisited' Lemma 16.** If the
`y`-partials are bounded in `y` for all but finitely many `x`, then so is the `x`-partial.
Partials are taken on the interior of the `C¹` locus. -/
theorem G4_bdd_dx (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) {n F D : ℕ}
    (f : (Fin (n + 1) → ℝ) → ℝ) (hf : graphOf f ∈ S.Ω F D (n + 1 + 1))
    (hI : ∀ z ∈ openCube (n + 1), f z ∈ Set.Ioo (0 : ℝ) 1)
    (hy : ∃ s : Finset ℝ, ∀ x ∈ Set.Ioo (0 : ℝ) 1, x ∉ s → ∃ B : ℝ, ∀ y ∈ openCube n,
      Fin.cons x y ∈ interior {z | ContDiffAt ℝ 1 f z} →
        ∀ i : Fin n, |fderiv ℝ f (Fin.cons x y) (Pi.single i.succ 1)| ≤ B) :
    ∃ s : Finset ℝ, ∀ x ∈ Set.Ioo (0 : ℝ) 1, x ∉ s → ∃ B : ℝ, ∀ y ∈ openCube n,
      Fin.cons x y ∈ interior {z | ContDiffAt ℝ 1 f z} →
        |fderiv ℝ f (Fin.cons x y) (Pi.single 0 1)| ≤ B := by
  sorry

/-- **G4c: the induction step** (BNZ §§5.2–5.5): bounded `y`-derivatives, 1-Lipschitz
reduction, control of higher derivatives along the `Γ_{i,α}` curves (affine `φ''=0`), and
clean-up. -/
theorem G4_step (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (n : ℕ) (hn : 1 ≤ n)
    (h1 : ∀ p, F1Affine S p) (ih : ∀ p, FLem S p n) : ∀ p, FLem S p (n + 1) := by
  sorry

/-- **G5: from F-lem to `AlgLemma`** (cell parametrisation of `X` by SharpCD, the shrink
`x ↦ (x+1)/3` into the open cube, conversion of operator norms, ε-cover bookkeeping). -/
theorem G5_alg_of_FLem (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (hF : ∀ p n, FLem S p n) (F n : ℕ) : AlgLemma S F n := by
  sorry

/-- **G wiring (proved):** `G_alg_lemma` from the holes. -/
theorem G_alg_lemma_wiring (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (F n : ℕ) :
    AlgLemma S F n := by
  have h1 : ∀ p, F1Affine S p := fun p => (G4_base S hcd hder p).2
  have hF : ∀ n p, FLem S p n := by
    intro n
    induction n with
    | zero => exact fun p => G4_zero S p
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; exact fun p => (G4_base S hcd hder p).1
      · exact G4_step S hcd hder n hpos h1 ih
  exact G5_alg_of_FLem S hcd hder (fun p n => hF n p) F n

end WilkiesDesign.CG
