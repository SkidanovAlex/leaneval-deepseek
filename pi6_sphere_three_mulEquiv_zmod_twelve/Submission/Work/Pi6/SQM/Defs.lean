import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.SQ.Defs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

/-!
# SQM — the lead's contracts for the middle of area SQ (DO NOT EDIT: every `Prop` is a contract)

Design: `REFS/NOTES_LEAD_SQM.md`.  Vocabulary of area SQ (`Work.Pi6.SQ.cup1m`, `Work.Pi6.SQ.cup2`,
Steenrod's interval convention) plus the cup-3 product `cup3` below (same convention).

Pieces (each ONE top-level lemma `Pi6/SQM/<name> : <Prop>`, all in parallel):
* `cup3Coboundary : Cup3Cob`, `cup1CoboundaryR : Cup1CobR`, `cupINatural : CupINatural`;
* `sigmaStar : SigmaStar` (cohomology suspension, the big one);
* `sqOneInjective : SqOneInjective`, `bocksteinSqTwo : Cup1CobR → Cup2Cob → BocksteinSqTwo`,
  `torsionOfNonliftable : TorsionOfNonliftable`;
* assemblies `sqCyclicCoreAsm`, `emExpAsm` (hypotheses = the Props above + area SQ's in-flight
  `sqOps`/`cartanInstance` statements, restated here as `SqOpsProp`, `CartanProp`).
-/

set_option autoImplicit false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff cohomologyClassOf)

/-- `𝔽₂`. -/
abbrev F2 : Type := Work.Pi6.SQ.F2

/-- The singular simplicial set of a space. -/
abbrev SX (X : Type) [TopologicalSpace X] : SSet := TopCat.toSSet.obj (TopCat.of X)

/-! ## The cup-3 product (Steenrod's interval formula, same convention as `SQ.cup2`)

For `u ∈ C^n`, `v ∈ C^m`, `N = n+m-3`, cut points `j₀ = a < j₁ = a+b < j₂ = a+b+c < j₃ = a+b+c+d`
with `d = m-1-b`: `U = [0,a] ∪ [j₁,j₂] ∪ [j₃,N]` (on `u`), `V = [a,j₁] ∪ [j₂,j₃]` (on `v`).
Checked against the general formula by `REFS/pi6_cup3param.py`. -/

/-- Left vertex map `⦋n⦌ → ⦋n+m-3⦌` of the `(a,b,c)`-term. -/
def cup3U (n m a b c : ℕ) (hb1 : 1 ≤ b) (hb2 : b + 2 ≤ m) (hc : 1 ≤ c) (hac : a + c + 2 ≤ n) :
    ⦋n⦌ ⟶ ⦋n + m - 3⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨if i.val ≤ a then i.val else
          if i.val ≤ a + c + 1 then i.val + b - 1 else i.val + m - 3, by
        have := i.isLt; simp only [SimplexCategory.len_mk] at this ⊢
        split_ifs <;> omega⟩
      monotone' := fun i j hij => by
        simp only [Fin.le_def] at hij ⊢
        split_ifs <;> omega }

/-- Right vertex map `⦋m⦌ → ⦋n+m-3⦌` of the `(a,b,c)`-term. -/
def cup3V (n m a b c : ℕ) (hb1 : 1 ≤ b) (hb2 : b + 2 ≤ m) (hc : 1 ≤ c) (hac : a + c + 2 ≤ n) :
    ⦋m⦌ ⟶ ⦋n + m - 3⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨if i.val ≤ b then a + i.val else i.val + a + c - 1, by
        have := i.isLt; simp only [SimplexCategory.len_mk] at this ⊢
        split_ifs <;> omega⟩
      monotone' := fun i j hij => by
        simp only [Fin.le_def] at hij ⊢
        split_ifs <;> omega }

/-- The value of `u ∪₃ v` on an `(n+m-3)`-simplex. -/
def cup3Val (X : SSet) (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m)
    (σ : X _⦋n + m - 3⦌) : F2 :=
  ∑ a : Fin (n - 2), ∑ b : Fin (m - 2), ∑ c : Fin (n - 2),
    if h : a.val + c.val + 3 ≤ n then
      genEval F2 X u (X.map (cup3U n m a.val (b.val + 1) (c.val + 1) (by omega)
        (by have := b.isLt; omega) (by omega) (by omega)).op σ) *
      genEval F2 X v (X.map (cup3V n m a.val (b.val + 1) (c.val + 1) (by omega)
        (by have := b.isLt; omega) (by omega) (by omega)).op σ)
    else 0

/-- `u ∪₃ v` as a linear map on chains. -/
def cup3Hom (X : SSet) (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m) :
    (X.chainComplex (ModuleCat.of F2 F2)).X (n + m - 3) ⟶ ModuleCat.of F2 F2 :=
  (X.isColimitChainComplexXCofan (ModuleCat.of F2 F2) (n + m - 3)).desc
    (Cofan.mk (ModuleCat.of F2 F2)
      (fun σ : X _⦋n + m - 3⦌ =>
        ModuleCat.ofHom (LinearMap.toSpanSingleton F2 F2 (cup3Val X n m u v σ))))

/-- **The mod-2 cup-3 product** `u ∪₃ v ∈ C^{n+m-3}(X;𝔽₂)`. -/
def cup3 (X : SSet) (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m) :
    Cochain F2 X (n + m - 3) := (cup3Hom X n m u v).hom

theorem genEval_cup3 (X : SSet) (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m)
    (σ : X _⦋n + m - 3⦌) : genEval F2 X (cup3 X n m u v) σ = cup3Val X n m u v σ := by
  have h1 : X.ιChainComplex (R := ModuleCat.of F2 F2) σ ≫ cup3Hom X n m u v =
      ModuleCat.ofHom (LinearMap.toSpanSingleton F2 F2 (cup3Val X n m u v σ)) :=
    Cofan.IsColimit.fac _ _ _
  have h2 := congrArg (fun (g : ModuleCat.of F2 F2 ⟶ ModuleCat.of F2 F2) => g.hom 1) h1
  simpa only [cup3, genEval, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] using h2

/-! ## Classes, liftability -/

/-- The class of a mod-2 cocycle on a space, in `H^n(X;𝔽₂)`. -/
abbrev cls {X : Type} [TopologicalSpace X] {n : ℕ} (x : Cochain F2 (SX X) n)
    (hx : cochainDiff F2 (SX X) x = 0) : Coh F2 X n :=
  cohomologyClassOf F2 (SX X) x hx

/-- Reduction `ℤ/4 → ℤ/2`. -/
abbrev r42 : ZMod 4 →+* ZMod 2 := ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)

/-- `c ∈ H^n(X;𝔽₂)` is the reduction of a `ℤ/4` class (⟺ the mod-2 Bockstein `β₂ c` vanishes). -/
def Liftable4 {X : Type} [TopologicalSpace X] {n : ℕ} (c : Coh F2 X n) : Prop :=
  ∃ (Y : Cochain (ZMod 4) (SX X) n) (_ : cochainDiff (ZMod 4) (SX X) Y = 0)
    (y : Cochain F2 (SX X) n) (hy : cochainDiff F2 (SX X) y = 0),
    cls y hy = c ∧ ∀ σ : (SX X) _⦋n⦌, r42 (genEval (ZMod 4) (SX X) Y σ) = genEval F2 (SX X) y σ

/-! ## Cochain-level formulas -/

/-- **Mod-2 coboundary formula for `∪₃`** (general cochains, `n, m ≥ 2`):
`δ(u∪₃v) = u∪₂v + v∪₂u + δu∪₃v + u∪₃δv`. -/
def Cup3Cob : Prop :=
  ∀ (X : SSet) (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m) (_hn : 2 ≤ n) (_hm : 2 ≤ m),
    (by omega : (n + m - 3) + 1 = n + m - 2) ▸ (cochainDiff F2 X (cup3 X n m u v)) =
      Work.Pi6.SQ.cup2 X n m u v + (by omega : m + n - 2 = n + m - 2) ▸ Work.Pi6.SQ.cup2 X m n v u +
      (by omega : (n + 1) + m - 3 = n + m - 2) ▸ cup3 X (n + 1) m (cochainDiff F2 X u) v +
      (by omega : n + (m + 1) - 3 = n + m - 2) ▸ cup3 X n (m + 1) u (cochainDiff F2 X v)

/-- **Mod-2 coboundary formula for `∪₂`** (restates area SQ's `cup2Coboundary`). -/
def Cup2Cob : Prop :=
  ∀ (X : SSet) (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m) (_hn : 1 ≤ n) (_hm : 1 ≤ m),
    (by omega : (n + m - 2) + 1 = n + m - 1) ▸ (cochainDiff F2 X (Work.Pi6.SQ.cup2 X n m u v)) =
      Work.Pi6.SQ.cup1m X n m u v + (by omega : m + n - 1 = n + m - 1) ▸ Work.Pi6.SQ.cup1m X m n v u +
      (by omega : (n + 1) + m - 2 = n + m - 1) ▸
        Work.Pi6.SQ.cup2 X (n + 1) m (cochainDiff F2 X u) v +
      (by omega : n + (m + 1) - 2 = n + m - 1) ▸
        Work.Pi6.SQ.cup2 X n (m + 1) u (cochainDiff F2 X v)

/-- **Mod-2 coboundary formula for `∪₁`** (general cochains). -/
def Cup1Cob : Prop :=
  ∀ (X : SSet) (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m) (_hn : 1 ≤ n) (_hm : 1 ≤ m),
    (by omega : (n + m - 1) + 1 = n + m) ▸ (cochainDiff F2 X (Work.Pi6.SQ.cup1m X n m u v)) =
      Work.Cohomology.cup F2 X u v + (Nat.add_comm m n) ▸ Work.Cohomology.cup F2 X v u +
      (by omega : (n + 1) + m - 1 = n + m) ▸ Work.Pi6.SQ.cup1m X (n + 1) m (cochainDiff F2 X u) v +
      (by omega : n + (m + 1) - 1 = n + m) ▸ Work.Pi6.SQ.cup1m X n (m + 1) u (cochainDiff F2 X v)

/-- **Integral (any `R`) coboundary formula for the library's `cup1`** (general cochains); signs
checked numerically by the lead (`REFS/pi6_int_cup1.py`): `ε₁ = -1`, `ε₂ = (-1)^(n+1)`. -/
def Cup1CobR : Prop :=
  ∀ (R : Type) [CommRing R] (X : SSet) (n m : ℕ) (α : Cochain R X n) (β : Cochain R X m)
    (_hn : 1 ≤ n) (_hm : 1 ≤ m),
    (by omega : (n + m - 1) + 1 = n + m) ▸ (cochainDiff R X (Work.Cohomology.cup1 R X n m α β)) =
      Work.Cohomology.cup R X α β -
        ((-1 : R) ^ (n * m)) • ((Nat.add_comm m n) ▸ Work.Cohomology.cup R X β α) -
      (by omega : (n + 1) + m - 1 = n + m) ▸
        Work.Cohomology.cup1 R X (n + 1) m (cochainDiff R X α) β +
      ((-1 : R) ^ (n + 1)) • ((by omega : n + (m + 1) - 1 = n + m) ▸
        Work.Cohomology.cup1 R X n (m + 1) α (cochainDiff R X β))

/-- **Naturality of `∪₁`, `∪₂`, `∪₃`** under maps of simplicial sets (pull-back of cochains). -/
def CupINatural : Prop :=
  ∀ (X Y : SSet) (f : X ⟶ Y) (n m : ℕ) (u : Cochain F2 Y n) (v : Cochain F2 Y m),
    Work.Pi6.SQ.cup1m X n m (((SSet.chainComplexMap f (ModuleCat.of F2 F2)).f n).hom.dualMap u)
        (((SSet.chainComplexMap f (ModuleCat.of F2 F2)).f m).hom.dualMap v) =
      ((SSet.chainComplexMap f (ModuleCat.of F2 F2)).f (n + m - 1)).hom.dualMap
        (Work.Pi6.SQ.cup1m Y n m u v) ∧
    Work.Pi6.SQ.cup2 X n m (((SSet.chainComplexMap f (ModuleCat.of F2 F2)).f n).hom.dualMap u)
        (((SSet.chainComplexMap f (ModuleCat.of F2 F2)).f m).hom.dualMap v) =
      ((SSet.chainComplexMap f (ModuleCat.of F2 F2)).f (n + m - 2)).hom.dualMap
        (Work.Pi6.SQ.cup2 Y n m u v) ∧
    cup3 X n m (((SSet.chainComplexMap f (ModuleCat.of F2 F2)).f n).hom.dualMap u)
        (((SSet.chainComplexMap f (ModuleCat.of F2 F2)).f m).hom.dualMap v) =
      ((SSet.chainComplexMap f (ModuleCat.of F2 F2)).f (n + m - 3)).hom.dualMap (cup3 Y n m u v)

/-- Area SQ's `sqOps`, restated (well-definedness of `[x∪₁x]` on H², H³ and `[x∪₂x]` on H³, H⁴). -/
def SqOpsProp : Prop :=
  (∀ (X : SSet) (x : Cochain F2 X 2) (_hx : cochainDiff F2 X x = 0) (w : Cochain F2 X 1),
    ∃ y : Cochain F2 X 2, cochainDiff F2 X y = Work.Pi6.SQ.cup1m X 2 2 x x +
      Work.Pi6.SQ.cup1m X 2 2 (x + cochainDiff F2 X w) (x + cochainDiff F2 X w)) ∧
  (∀ (X : SSet) (x : Cochain F2 X 3) (_hx : cochainDiff F2 X x = 0) (w : Cochain F2 X 2),
    ∃ y : Cochain F2 X 4, cochainDiff F2 X y = Work.Pi6.SQ.cup1m X 3 3 x x +
      Work.Pi6.SQ.cup1m X 3 3 (x + cochainDiff F2 X w) (x + cochainDiff F2 X w)) ∧
  (∀ (X : SSet) (x : Cochain F2 X 3) (_hx : cochainDiff F2 X x = 0) (w : Cochain F2 X 2),
    ∃ y : Cochain F2 X 3, cochainDiff F2 X y = Work.Pi6.SQ.cup2 X 3 3 x x +
      Work.Pi6.SQ.cup2 X 3 3 (x + cochainDiff F2 X w) (x + cochainDiff F2 X w)) ∧
  (∀ (X : SSet) (x : Cochain F2 X 4) (_hx : cochainDiff F2 X x = 0) (w : Cochain F2 X 3),
    ∃ y : Cochain F2 X 5, cochainDiff F2 X y = Work.Pi6.SQ.cup2 X 4 4 x x +
      Work.Pi6.SQ.cup2 X 4 4 (x + cochainDiff F2 X w) (x + cochainDiff F2 X w))

/-- Area SQ's `cartanInstance`, restated. -/
def CartanProp : Prop :=
  ∀ (X : SSet) (x : Cochain F2 X 2), cochainDiff F2 X x = 0 →
    cochainDiff F2 X (Work.Pi6.SQ.cartanCochain X x) =
      Work.Pi6.SQ.cup2 X 4 4 (Work.Cohomology.cup F2 X x x) (Work.Cohomology.cup F2 X x x) +
      Work.Cohomology.cup F2 X (Work.Pi6.SQ.cup1m X 2 2 x x) (Work.Pi6.SQ.cup1m X 2 2 x x)

/-! ## Cohomology-level pieces -/

/-- **The cohomology suspension `σ* : H^{n+1}(K;𝔽₂) → H^n(ΩK;𝔽₂)`** (`ΩK = Path k₀ k₀`) with:
(b) naturality for based maps; (c1)–(c5) `σ*` commutes with the Steenrod squares used
(`σ*[x∪ᵢx] = [z∪_{i-1}z]` for any cocycle `z` representing `σ*[x]`); (d) bijective for
`n+2 < 2b`, injective for `n+2 = 2b`, `n ≥ 1`, when `K` is `(b-1)`-connected; (e) `σ*` preserves
`ℤ/4`-liftability.  Route: `REFS/NOTES_LEAD_SQM.md` §1. -/
def SigmaStar : Prop :=
  ∃ σ : ∀ (K : Type) [TopologicalSpace K] (k₀ : K) (n : ℕ),
      Coh F2 K (n + 1) →ₗ[F2] Coh F2 (Path k₀ k₀) n,
    -- (b) naturality
    (∀ (K L : Type) [TopologicalSpace K] [TopologicalSpace L] (k₀ : K) (h : C(K, L))
        (Ωh : C(Path k₀ k₀, Path (h k₀) (h k₀))), (∀ γ t, Ωh γ t = h (γ t)) →
        ∀ (n : ℕ) (z : Coh F2 L (n + 1)),
          σ K k₀ n (cmap F2 h (n + 1) z) = cmap F2 Ωh n (σ L (h k₀) n z)) ∧
    -- (c1) Sq² on H³ ↦ square on H²
    (∀ (K : Type) [TopologicalSpace K] (k₀ : K) (x : Cochain F2 (SX K) 3)
        (hx : cochainDiff F2 (SX K) x = 0)
        (hxx : cochainDiff F2 (SX K) (Work.Pi6.SQ.cup1m (SX K) 3 3 x x) = 0)
        (z : Cochain F2 (SX (Path k₀ k₀)) 2) (hz : cochainDiff F2 (SX (Path k₀ k₀)) z = 0)
        (hzz : cochainDiff F2 (SX (Path k₀ k₀)) (Work.Cohomology.cup F2 (SX (Path k₀ k₀)) z z) = 0),
        cls z hz = σ K k₀ 2 (cls x hx) →
        σ K k₀ 4 (cls (Work.Pi6.SQ.cup1m (SX K) 3 3 x x) hxx) =
          cls (Work.Cohomology.cup F2 (SX (Path k₀ k₀)) z z) hzz) ∧
    -- (c2) Sq¹ on H⁴ (∪₃) ↦ Sq¹ on H³ (∪₂)
    (∀ (K : Type) [TopologicalSpace K] (k₀ : K) (x : Cochain F2 (SX K) 4)
        (hx : cochainDiff F2 (SX K) x = 0) (hxx : cochainDiff F2 (SX K) (cup3 (SX K) 4 4 x x) = 0)
        (z : Cochain F2 (SX (Path k₀ k₀)) 3) (hz : cochainDiff F2 (SX (Path k₀ k₀)) z = 0)
        (hzz : cochainDiff F2 (SX (Path k₀ k₀)) (Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 3 3 z z) = 0),
        cls z hz = σ K k₀ 3 (cls x hx) →
        σ K k₀ 4 (cls (cup3 (SX K) 4 4 x x) hxx) =
          cls (Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 3 3 z z) hzz) ∧
    -- (c3) Sq¹ on H³ (∪₂) ↦ Sq¹ on H² (∪₁)
    (∀ (K : Type) [TopologicalSpace K] (k₀ : K) (x : Cochain F2 (SX K) 3)
        (hx : cochainDiff F2 (SX K) x = 0)
        (hxx : cochainDiff F2 (SX K) (Work.Pi6.SQ.cup2 (SX K) 3 3 x x) = 0)
        (z : Cochain F2 (SX (Path k₀ k₀)) 2) (hz : cochainDiff F2 (SX (Path k₀ k₀)) z = 0)
        (hzz : cochainDiff F2 (SX (Path k₀ k₀)) (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 z z) = 0),
        cls z hz = σ K k₀ 2 (cls x hx) →
        σ K k₀ 3 (cls (Work.Pi6.SQ.cup2 (SX K) 3 3 x x) hxx) =
          cls (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 2 2 z z) hzz) ∧
    -- (c4) Sq² on H⁵ (∪₃) ↦ Sq² on H⁴ (∪₂)
    (∀ (K : Type) [TopologicalSpace K] (k₀ : K) (x : Cochain F2 (SX K) 5)
        (hx : cochainDiff F2 (SX K) x = 0) (hxx : cochainDiff F2 (SX K) (cup3 (SX K) 5 5 x x) = 0)
        (z : Cochain F2 (SX (Path k₀ k₀)) 4) (hz : cochainDiff F2 (SX (Path k₀ k₀)) z = 0)
        (hzz : cochainDiff F2 (SX (Path k₀ k₀)) (Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 4 4 z z) = 0),
        cls z hz = σ K k₀ 4 (cls x hx) →
        σ K k₀ 6 (cls (cup3 (SX K) 5 5 x x) hxx) =
          cls (Work.Pi6.SQ.cup2 (SX (Path k₀ k₀)) 4 4 z z) hzz) ∧
    -- (c5) Sq² on H⁴ (∪₂) ↦ Sq² on H³ (∪₁)
    (∀ (K : Type) [TopologicalSpace K] (k₀ : K) (x : Cochain F2 (SX K) 4)
        (hx : cochainDiff F2 (SX K) x = 0)
        (hxx : cochainDiff F2 (SX K) (Work.Pi6.SQ.cup2 (SX K) 4 4 x x) = 0)
        (z : Cochain F2 (SX (Path k₀ k₀)) 3) (hz : cochainDiff F2 (SX (Path k₀ k₀)) z = 0)
        (hzz : cochainDiff F2 (SX (Path k₀ k₀)) (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 3 3 z z) = 0),
        cls z hz = σ K k₀ 3 (cls x hx) →
        σ K k₀ 5 (cls (Work.Pi6.SQ.cup2 (SX K) 4 4 x x) hxx) =
          cls (Work.Pi6.SQ.cup1m (SX (Path k₀ k₀)) 3 3 z z) hzz) ∧
    -- (d) range
    (∀ (K : Type) [TopologicalSpace K] (k₀ : K) (b : ℕ), 2 ≤ b →
        (∀ i : ℕ, i < b → Subsingleton (HomotopyGroup (Fin i) K k₀)) →
        ∀ n : ℕ, 1 ≤ n →
          (n + 2 < 2 * b → Function.Bijective (σ K k₀ n)) ∧
          (n + 2 = 2 * b → Function.Injective (σ K k₀ n))) ∧
    -- (e) liftability
    (∀ (K : Type) [TopologicalSpace K] (k₀ : K) (n : ℕ) (c : Coh F2 K (n + 1)),
        Liftable4 c → Liftable4 (σ K k₀ n c))

/-- **`Sq¹` is injective on `H²` when `H₁(X;ℤ) = 0` and `2·H₂(X;ℤ) = 0`** (`[x∪₁x] = 0 ⇒ [x] = 0`). -/
def SqOneInjective : Prop :=
  ∀ (X : Type) [TopologicalSpace X], Subsingleton (HR ℤ X 1) →
    (∀ a : HR ℤ X 2, (2 : ℤ) • a = 0) →
    ∀ (x : Cochain F2 (SX X) 2) (hx : cochainDiff F2 (SX X) x = 0)
      (hxx : cochainDiff F2 (SX X) (Work.Pi6.SQ.cup1m (SX X) 2 2 x x) = 0),
      cls (Work.Pi6.SQ.cup1m (SX X) 2 2 x x) hxx = 0 → cls x hx = 0

/-- **`β₂ Sq² = Sq³` on `H³`**: if `[x∪₁x]` lifts to `ℤ/4` then `[x∪x] = 0`. -/
def BocksteinSqTwo : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (x : Cochain F2 (SX X) 3) (hx : cochainDiff F2 (SX X) x = 0)
    (hxx : cochainDiff F2 (SX X) (Work.Pi6.SQ.cup1m (SX X) 3 3 x x) = 0)
    (hsq : cochainDiff F2 (SX X) (Work.Cohomology.cup F2 (SX X) x x) = 0),
    Liftable4 (cls (Work.Pi6.SQ.cup1m (SX X) 3 3 x x) hxx) →
      cls (Work.Cohomology.cup F2 (SX X) x x) hsq = 0

/-- **A non-liftable mod-2 class of degree `n` gives an element of `H_n(X;ℤ)` of order ≤ 2 that is
not divisible by 2.** -/
def TorsionOfNonliftable : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (n : ℕ) (y : Cochain F2 (SX X) n)
    (hy : cochainDiff F2 (SX X) y = 0), ¬ Liftable4 (cls y hy) →
    ∃ a : HR ℤ X n, (2 : ℤ) • a = 0 ∧ ∀ b : HR ℤ X n, (2 : ℤ) • b ≠ a

end

end Work.Pi6.SQM
