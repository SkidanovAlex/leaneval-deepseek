import Submission.Work.PL.Defs

/-!
# Newman's engulfing theorem (area A9): definitions

This is the definition layer of area A9 (`Work.Engulf`) of
`Submission/Work/NOTES_LEAD_poincare_engulf.md`.  It is the *verbatim* definition part of the
typechecked skeleton `Submission/Work/Engulf/Skeleton.lean` (the lead's design pass), split off
into its own module so that the rest of the area can import it.

Vocabulary comes from `Submission.Work.PL.Defs` (`PL.E`, `PL.Cx`, `PL.simp`, `PL.closedCube`,
`PL.openCube`, `PL.CubeChart`, `PL.DomDim`, `PL.LocCube`, `PL.ExtOverDisc`, `PL.CSupp`,
`PL.Subdivides`, `PL.MeshLT`, `PL.DimLE`).

Conventions (see the contract §§5, 9):
* the ambient space is a *fixed* `PL.E N` with room `2p + 4 ≤ N`, cone apices generic;
* `IsSubSp Γ S` = `S` is a union of closed faces of `Γ` (Newman's subcomplexes are sets here);
* `Tame` is defined by *local* linearity (stable under shrinking charts);
* `Engulfs` does not mention isotopies: it produces a compactly supported homeomorphism;
* the invariants of §9 carry only the `q`-skeleton of already-pushed simplices, *not* their
  interiors (this is Newman's (13.2) and is essential at `q = n - 3`).
-/

open Set Metric PL

namespace Work.Engulf

universe u

variable {n : ℕ} {M : Type*} [MetricSpace M] {N : ℕ}

/-- `S` is a union of closed faces of `Γ` (the space of a subcomplex). -/
def IsSubSp (Γ : Cx N) (S : Set (E N)) : Prop :=
  S ⊆ Γ.space ∧ ∀ x ∈ S, ∃ s ∈ Γ.faces, x ∈ simp s ∧ simp s ⊆ S

/-- `f` is `ψ`-affine on `S`, with chart coordinates in the open unit cube. -/
def LinIn (ψ : CubeChart n M) (f : E N → M) (S : Set (E N)) : Prop :=
  ∃ A : E N →ᵃ[ℝ] E n, ∀ y ∈ S, A y ∈ openCube (1 : ℝ) ∧ f y = ψ.toFun (A y)

/-- `X` is `p`-dominated in the chart `ψ` (Newman §9). -/
def DomIn (p : ℕ) (ψ : CubeChart n M) (X : Set M) : Prop :=
  ∃ P : Set (E n), DomDim P p ∧ ∀ y ∈ closedCube (1 : ℝ), ψ.toFun y ∈ X → y ∈ P

/-- `ψ` is a smoothing chart for `X` and for `f` on the frozen faces (Newman (9.3)). -/
def SmoothChart (p : ℕ) (X : Set M) (Γ : Cx N) (L : Set (E N)) (f : E N → M)
    (ψ : CubeChart n M) : Prop :=
  DomIn p ψ X ∧ ∀ s ∈ Γ.faces, simp s ⊆ L → ∀ y ∈ simp s,
    f y ∈ ψ.toFun '' closedCube (3 / 4 : ℝ) → ∃ δ > 0, LinIn ψ f (simp s ∩ ball y δ)

/-- Newman (9.3): a smoothing system through every point of `M`. -/
def Tame (n p : ℕ) (X : Set M) (Γ : Cx N) (L : Set (E N)) (f : E N → M) : Prop :=
  ∀ x : M, ∃ ψ : CubeChart n M, x ∈ ψ.toFun '' openCube (1 / 2 : ℝ) ∧ SmoothChart p X Γ L f ψ

/-- Overlap control (replaces "f|L is an embedding"): frozen points of `H` collide with each
other, or hit `X`, only over a compact set mapped into `V`. -/
def OvCtl (V X : Set M) (H L : Set (E N)) (f : E N → M) : Prop :=
  ∃ C : Set (E N), IsCompact C ∧ f '' C ⊆ V ∧
    (∀ x ∈ H ∩ L, ∀ y ∈ H ∩ L, f x = f y → x ≠ y → x ∈ C) ∧
    (∀ x ∈ H ∩ L, f x ∈ X → x ∈ C)

/-- Faces of `Γ` inside `H` not mapped into `V` have at most `k` vertices. -/
def BadCard (Γ : Cx N) (H : Set (E N)) (f : E N → M) (V : Set M) (k : ℕ) : Prop :=
  ∀ s ∈ Γ.faces, simp s ⊆ H → ¬ (f '' simp s ⊆ V) → s.card ≤ k

/-- Ambient hypotheses of Theorem 6 (fixed along the recursion up to `V ↦ h '' V`). -/
structure Amb (n p : ℕ) (M : Type*) [MetricSpace M] (V : Set M) : Prop where
  hp : p + 3 ≤ n
  loc : LocCube n M
  connM : ∀ j ≤ p, ExtOverDisc M j
  Vo : IsOpen V
  Vne : V.Nonempty
  connV : ∀ j, j + 1 ≤ p → ExtOverDisc V j

/-- Configuration hypotheses of Theorem 6 ((9.1)–(9.3) as used). -/
structure Cfg (n p : ℕ) (V X : Set M) (Γ : Cx N) (H L : Set (E N)) (f : E N → M) : Prop where
  fin : Γ.faces.Finite
  dimΓ : DimLE Γ (p + 1)
  room : 2 * p + 4 ≤ N
  subH : IsSubSp Γ H
  subL : IsSubSp Γ L
  dimH : ∀ s ∈ Γ.faces, simp s ⊆ H → s.card ≤ p + 1
  cont : ContinuousOn f Γ.space
  Xc : IsClosed X
  cpt : IsCompact ((X ∪ f '' H) \ V)
  tame : Tame n p X Γ L f
  ov : OvCtl V X H L f

/-- Conclusion (9.4)–(9.6) (without "f = g off a compact set"). -/
def Engulfs (V X : Set M) (Γ : Cx N) (H L : Set (E N)) (f : E N → M) (ε : ℝ) : Prop :=
  ∃ g : E N → M, ContinuousOn g Γ.space ∧ EqOn g f L ∧ (∀ x ∈ Γ.space, dist (g x) (f x) < ε) ∧
    ∃ h : M ≃ₜ M, CSupp h univ ∧ X ∪ g '' H ⊆ h '' V

/-- Newman's `B(k-1)`: Theorem 6 with `X ⊆ V` and bad faces of `H` of card `≤ k`. -/
def B (n p k : ℕ) : Prop :=
  ∀ (M : Type u) [MetricSpace M] (V X : Set M) (N : ℕ) (Γ : Cx N) (H L : Set (E N))
    (f : E N → M), Amb n p M V → Cfg n p V X Γ H L f → X ⊆ V → BadCard Γ H f V k →
    ∀ ε > 0, Engulfs V X Γ H L f ε

/-- Newman's `C(q,1)` with `k = q + 1 = σ.card`, plus the clean condition. -/
def C1 (n p k : ℕ) : Prop :=
  ∀ (M : Type u) [MetricSpace M] (V X : Set M) (N : ℕ) (Γ : Cx N) (H L : Set (E N))
    (f : E N → M) (σ : Finset (E N)), Amb n p M V → Cfg n p V X Γ H L f → X ⊆ V →
    σ ∈ Γ.faces → σ.card = k → simp σ ⊆ H →
    (∀ s ∈ Γ.faces, simp s ⊆ H → σ ⊆ s → s = σ) →
    (∀ s ∈ Γ.faces, simp s ⊆ H → s ≠ σ → f '' simp s ⊆ V) →
    Disjoint (f '' simp σ) X →
    (∀ x ∈ simp σ ∩ L, ∀ y ∈ H ∩ L, f x = f y → x = y) →
    ∀ ε > 0, Engulfs V X Γ H L f ε

/-- floor `τ₀ τ̇₁` and top `τ̇₀ τ₁` of the join `τ₀ ∪ τ₁` (G2 naming; Newman σ₁ = τ₀, σ₂ = τ₁). -/
def floorOf (τ₀ τ₁ : Finset (E N)) : Set (E N) := ⋃ w ∈ τ₁, simp ((τ₀ ∪ τ₁).erase w)
def topOf (τ₀ τ₁ : Finset (E N)) : Set (E N) := ⋃ w ∈ τ₀, simp ((τ₀ ∪ τ₁).erase w)

/-- Lemma 7 hypotheses for the join `Δ = τ₀ ∪ τ₁` of card `q + 2`. -/
structure L7Hyp (n p q : ℕ) (V X : Set M) (Γ : Cx N) (K L : Set (E N)) (f : E N → M)
    (τ₀ τ₁ : Finset (E N)) : Prop where
  cfg : Cfg n p V X Γ (K ∪ topOf τ₀ τ₁) L f
  hq : q ≤ p
  mem : τ₀ ∪ τ₁ ∈ Γ.faces
  ne₀ : τ₀.Nonempty
  ne₁ : τ₁.Nonempty
  disj : Disjoint τ₀ τ₁
  card : (τ₀ ∪ τ₁).card = q + 2
  subK : IsSubSp Γ K
  meetK : K ∩ simp (τ₀ ∪ τ₁) = floorOf τ₀ τ₁                 -- (12.1)
  engK : X ∪ f '' K ⊆ V                                       -- (12.2)
  offX : Disjoint (f '' (L ∩ simp (τ₀ ∪ τ₁))) X                -- (12.3)
  free : ∃ A : AffineSubspace ℝ (E N),
    Module.finrank ℝ A.direction ≤ q ∧ L ∩ simp (τ₀ ∪ τ₁) ⊆ A   -- frozen part in a q-plane
  clean : ∀ x ∈ simp (τ₀ ∪ τ₁) ∩ L, ∀ y ∈ (K ∪ simp (τ₀ ∪ τ₁)) ∩ L, f x = f y → x = y

def L7 (n p q : ℕ) : Prop :=
  ∀ (M : Type u) [MetricSpace M] (V X : Set M) (N : ℕ) (Γ : Cx N) (K L : Set (E N))
    (f : E N → M) (τ₀ τ₁ : Finset (E N)), Amb n p M V → L7Hyp n p q V X Γ K L f τ₀ τ₁ →
    ∀ ε > 0, Engulfs V X Γ (K ∪ topOf τ₀ τ₁) L f ε

/-- Lemma 7, Case 1 (12.5): the simplex lies in one smoothing chart. -/
def L7c (n p q : ℕ) : Prop :=
  ∀ (M : Type u) [MetricSpace M] (V X : Set M) (N : ℕ) (Γ : Cx N) (K L : Set (E N))
    (f : E N → M) (τ₀ τ₁ : Finset (E N)) (ψ : CubeChart n M), Amb n p M V →
    L7Hyp n p q V X Γ K L f τ₀ τ₁ → SmoothChart p X Γ L f ψ →
    f '' simp (τ₀ ∪ τ₁) ⊆ ψ.toFun '' openCube (1 / 2 : ℝ) →
    ∀ ε > 0, Engulfs V X Γ (K ∪ topOf τ₀ τ₁) L f ε


/-! ## The §7.2 tools and the §9 invariants (verbatim from the skeleton) -/

structure InnerInv (n p : ℕ) (V X : Set M) (Γ₁ : Cx N) (K L Rc : Set (E N)) (g₁ : E N → M)
    (ord : List (Finset (E N))) (η : ℝ) (i : ℕ) (Γc : Cx N) (g : E N → M) (h : M ≃ₜ M) : Prop where
  le : i ≤ ord.length
  sub : Γ₁.faces ⊆ Γc.faces
  finc : Γc.faces.Finite
  dimc : DimLE Γc (p + 1)
  cont : ContinuousOn g Γc.space
  frz : EqOn g g₁ (L ∪ Rc)
  near : ∀ x ∈ Γ₁.space, dist (g x) (g₁ x) < i * η
  supp : CSupp h univ
  eng : X ∪ g '' (K ∪ ⋃ j ∈ Finset.range i, ⋃ (hj : j < ord.length),
          ⋃ w ∈ ord[j], simp (ord[j].erase w)) ⊆ h '' V

structure SubdivTools (N : ℕ) where
  sdIter : ℕ → (K : Cx N) → K.faces.Finite → Cx N
  fin    : ∀ r K hK, (sdIter r K hK).faces.Finite
  zero   : ∀ K hK, sdIter 0 K hK = K
  subdiv : ∀ r K hK, Subdivides (sdIter r K hK) K
  subsp  : ∀ r K hK (S : Set (E N)), IsSubSp K S → IsSubSp (sdIter r K hK) S
  dimle  : ∀ r K hK d, DimLE K d → DimLE (sdIter r K hK) d
  fine   : ∀ K hK δ, 0 < δ → ∃ r, ∀ r' ≥ r, MeshLT (sdIter r' K hK) δ
  shell  : ∀ r K hK (Δ τ₁ : Finset (E N)), Δ ∈ K.faces → τ₁.Nonempty → τ₁ ⊂ Δ →
    ∃ ord : List (Finset (E N)), ord.Nodup ∧
      (∀ τ ∈ ord, τ ∈ (sdIter r K hK).faces ∧ τ.card = Δ.card ∧ simp τ ⊆ simp Δ) ∧
      (⋃ τ ∈ ord, simp τ) = simp Δ ∧
      ∀ i (hi : i < ord.length), ∃ τ₁' : Finset (E N), τ₁'.Nonempty ∧ τ₁' ⊂ ord[i] ∧
        simp ord[i] ∩ ((⋃ w ∈ τ₁, simp (Δ.erase w)) ∪ ⋃ j ∈ Finset.range i, ⋃ (hj : j < ord.length),
          simp ord[j]) = ⋃ w ∈ τ₁', simp (ord[i].erase w)

def PlApproxFrozenForm (S : SubdivTools N) (n : ℕ) : Prop :=
  ∀ (K : Cx N) (hK : K.faces.Finite) (L : Set (E N)), IsSubSp K L →
    ∀ (f : E N → E n), ContinuousOn f K.space → ∀ (α β : ℝ), 0 < α → α < β → β < 1 →
    (∀ s ∈ K.faces, simp s ⊆ L → (∃ x ∈ simp s, f x ∈ closedCube β) →
        ∃ A : E N →ᵃ[ℝ] E n, EqOn f A (simp s)) →
    ∀ ε > 0, ∃ r, ∃ g : E N → E n, ContinuousOn g K.space ∧
      (∀ x ∈ K.space, dist (g x) (f x) < ε) ∧ EqOn g f L ∧
      (∀ x ∈ K.space, f x ∉ closedCube β → g x = f x) ∧
      ∀ s ∈ (S.sdIter r K hK).faces, (∃ x ∈ simp s, g x ∈ closedCube α) →
        ∃ A : E N →ᵃ[ℝ] E n, EqOn g A (simp s)

def VertexPerturbForm (N n : ℕ) : Prop :=
  ∀ (K : Cx N) (hK : K.faces.Finite) (Z : Finset (E N)) (g : E N → E n), ContinuousOn g K.space →
    (∀ v ∈ Z, ∃ s ∈ K.faces, v ∈ s) →
    (∀ s ∈ K.faces, (∃ v ∈ s, v ∈ Z) → ∃ A : E N →ᵃ[ℝ] E n, EqOn g A (simp s)) →
    ∀ (y : E N → E n) (η : ℝ), 0 ≤ η → (∀ v ∈ Z, dist (y v) (g v) ≤ η) →
    ∃ g' : E N → E n, ContinuousOn g' K.space ∧ (∀ v ∈ Z, g' v = y v) ∧
      (∀ s ∈ K.faces, (∀ v ∈ s, v ∉ Z) → EqOn g' g (simp s)) ∧
      (∀ s ∈ K.faces, (∃ v ∈ s, v ∈ Z) → ∃ A : E N →ᵃ[ℝ] E n, EqOn g' A (simp s) ∧
          ∀ v ∈ s, v ∉ Z → A v = g v) ∧
      ∀ x ∈ K.space, dist (g' x) (g x) ≤ η

def hullOf {ι : Type*} {n : ℕ} (y : ι → E n) (s : Finset ι) : Set (E n) :=
  convexHull ℝ (y '' (s : Set ι))

--  (G6a′) is owned by area PL/Generic (A3): see NOTES_LEAD_poincare_engulf.md §4.1.

structure E2Inv (V X : Set M) (Γ₁ : Cx N) (L P₁ Sk : Set (E N)) (f : E N → M)
    (bad : List (Finset (E N))) (η₀ η : ℝ) (j : ℕ) (g : E N → M) (h : M ≃ₜ M) : Prop where
  le   : j ≤ bad.length
  cont : ContinuousOn g Γ₁.space
  frz  : EqOn g f L
  near : ∀ x ∈ Γ₁.space, dist (g x) (f x) < η₀ + j * η
  supp : CSupp h univ
  eng  : X ∪ g '' (P₁ ∪ Sk ∪ ⋃ i ∈ Finset.range j, ⋃ (hi : i < bad.length), simp bad[i]) ⊆ h '' V
  offX : ∀ i (hi : i < bad.length), j ≤ i → Disjoint (g '' simp bad[i]) X

structure E1Inv (p : ℕ) (V X' : Set M) (Γ : Cx N) (H L : Set (E N)) (f : E N → M)
    (pieces : List (Finset (E N))) (pmap : ℕ → (E N → M)) (η : ℝ) (r : ℕ)
    (Γr : Cx N) (g : E N → M) (h : M ≃ₜ M) : Prop where
  sub  : Γ.faces ⊆ Γr.faces
  fin  : Γr.faces.Finite
  dim  : DimLE Γr (p + 1)
  cont : ContinuousOn g Γr.space
  frz  : EqOn g f L
  frzP : ∀ j < r, ∀ (hj : j < pieces.length), EqOn g (pmap j) (simp pieces[j])
  near : ∀ x ∈ Γ.space, dist (g x) (f x) < (r + 1) * η
  supp : CSupp h univ
  eng  : X' ∪ g '' (H ∪ ⋃ j ∈ Finset.range r, ⋃ (hj : j < pieces.length), simp pieces[j]) ⊆ h '' V

structure PieceInv (n p : ℕ) (V X : Set M) (Γ₁ : Cx N) (K L Rc : Set (E N)) (g₁ : E N → M)
    (ord : List (Finset (E N))) (η' : ℝ) (i : ℕ) (pieces : List (Finset (E N)))
    (pmap : ℕ → (E N → M)) (k : ℕ) (Γc : Cx N) (g : E N → M) (h : M ≃ₜ M) : Prop where
  base : InnerInv n p V X Γ₁ K L Rc g₁ ord η' i Γc g h
  frzP : ∀ j < k, ∀ (hj : j < pieces.length), EqOn g (pmap j) (simp pieces[j])
  inΓ  : ∀ j < k, ∀ (hj : j < pieces.length), IsSubSp Γc (simp pieces[j])
  engP : X ∪ g '' (⋃ j ∈ Finset.range k, ⋃ (hj : j < pieces.length), simp pieces[j]) ⊆ h '' V


end Work.Engulf
