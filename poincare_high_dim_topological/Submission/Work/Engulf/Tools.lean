import Submission.Work.Engulf.Defs

/-!
# Area A9: the hypotheses taken from the other areas ("Forms")

`Submission/Work/NOTES_LEAD_poincare_engulf.md` §7: the engulfing chapter (A9) does **not** wait
for the other areas of the blueprint.  It takes their results as `Prop`-valued *forms* (exactly
as A8 does with `Work.Cells.Connell.Assumptions`), proves

    Tools -> (B(k) and C(q,1) chain) -> EngulfForm n,

and the lead later replaces each form by the real theorem of the area that owns it.

The forms, and their owners:

* `PrismPushForm`      — A1, blueprint `G1` (`prism_push`, Newman §1 Thm 1, Case 1);
* `PrismPushRelForm`   — A1, blueprint `G1'` (`prism_push_rel`, Newman Thm 2), the form §14 uses;
* `JoinPrismForm`      — A1, blueprint `G2` (`join_simplex_prism`, Newman §13);
* `SimplexBallForm`    — A2 item 8 (`simplex_homeo_disc`);
* `SubdivToolsExt`     — A2 + A4, blueprint `G3`/`G4` (`sdIter`, mesh, and the shelling);
* `GPaForm`            — A3, the *corrected* general-position statement `G6a'` of §4.1;
* `PlApproxFrozenForm` — A5, blueprint `G5` (frozen variant), the form E4 consumes;
* `VertexPerturbForm`  — A5/A9, the vertex perturbation realising `G6a'` (§7.2, aux Hx8);
* `ExtHomeoOpenForm`   — A7, blueprint `C0` (`ext_homeo_open`).

Everything is bundled in `Tools N n` (`N` = the ambient dimension, `n` = `dim M`).
-/

open Set Metric PL

namespace Work.Engulf

universe u

variable {n : ℕ} {M : Type*} [MetricSpace M] {N : ℕ}

/-! ## The prism (A1, blueprint G1, G1', G2) -/

/-- The prism space `Pr a b = E a × E b × ℝ`: `(y, z, t)`, `y` the thickness direction,
`z` the base direction, `t` the stretch direction.  Same as `Work.Geo.Prism.Pr` (definitionally
equal; A9 keeps its own copy so that the chapter does not depend on area A1's files). -/
abbrev Pr (a b : ℕ) : Type := E a × E b × ℝ

/-- **A1, blueprint `G1`** (`prism_push`, Newman §1 Lemma 2 + Theorem 1 Case 1). -/
def PrismPushForm : Prop :=
  ∀ {a b : ℕ} (F : Set (E b)), IsCompact F → ∀ (φ γ : E b → ℝ), Continuous φ → Continuous γ →
    (∀ z ∈ F, φ z ≤ γ z) → (∀ z ∈ frontier F, φ z = γ z) →
    ∀ (U W : Set (Pr a b)), IsOpen U → IsOpen W →
    (∀ z ∈ F, ((0 : E a), z, φ z) ∈ U) →
    (∀ z ∈ F, ∀ t, φ z ≤ t → t ≤ γ z → ((0 : E a), z, t) ∈ W) →
    ∃ h : Pr a b ≃ₜ Pr a b, CSupp h W ∧
      (∀ y z t, (z ∉ F ∨ t ≤ φ z) → h (y, z, t) = (y, z, t)) ∧
      (∀ y z t, (h (y, z, t)).1 = y ∧ (h (y, z, t)).2.1 = z) ∧
      (∀ z ∈ F, ∀ t, φ z ≤ t → t ≤ γ z → ((0 : E a), z, t) ∈ h '' U)

/-- **A1, blueprint `G1'`** (`prism_push_rel`, Newman Theorem 2): the form §14 uses.
`hAS` is the `E4b` input: the only points of the prism that are in the closed set `A` are the
floor points and those over `J`. -/
def PrismPushRelForm : Prop :=
  ∀ {a b : ℕ} (F J : Set (E b)), IsCompact F → IsClosed J → J ⊆ F →
    ∀ (γ₀ γ₁ : E b → ℝ), Continuous γ₀ → Continuous γ₁ → (∀ z ∈ F, γ₀ z ≤ γ₁ z) →
    (∀ z ∈ frontier F, γ₀ z = γ₁ z) → ∀ (U W A : Set (Pr a b)), IsOpen U → IsOpen W →
    IsClosed A → A ⊆ U →
    (∀ z ∈ F, ((0 : E a), z, γ₀ z) ∈ U) →
    (∀ z ∈ J, ∀ t ∈ Icc (γ₀ z) (γ₁ z), ((0 : E a), z, t) ∈ U) →
    (∀ z ∈ F, ∀ t ∈ Icc (γ₀ z) (γ₁ z), ((0 : E a), z, t) ∈ W) →
    (∀ z ∈ F, ∀ t ∈ Icc (γ₀ z) (γ₁ z), ((0 : E a), z, t) ∈ A → t = γ₀ z ∨ z ∈ J) →
    ∃ h : Pr a b ≃ₜ Pr a b, CSupp h W ∧ (∀ x ∈ A, h x = x) ∧
      ∀ z ∈ F, ∀ t ∈ Icc (γ₀ z) (γ₁ z), ((0 : E a), z, t) ∈ h '' U

/-- **A1, blueprint `G2`** (`join_simplex_prism`, Newman §13). -/
def JoinPrismForm (N : ℕ) : Prop :=
  ∀ {q : ℕ} (hq : q + 1 ≤ N) (τ₀ τ₁ : Finset (E N)), τ₀.Nonempty → τ₁.Nonempty →
    Disjoint τ₀ τ₁ → (τ₀ ∪ τ₁).card = q + 2 →
    AffineIndependent ℝ (fun v : ↥(τ₀ ∪ τ₁) => ((v : E N))) →
    ∃ (T : E N ≃ᵃ[ℝ] Pr (N - q - 1) q) (F : Set (E q)) (γ₀ γ₁ : E q → ℝ),
      IsCompact F ∧ Convex ℝ F ∧ Continuous γ₀ ∧ Continuous γ₁ ∧
      (∀ z ∈ F, γ₀ z ≤ γ₁ z) ∧ (∀ z ∈ frontier F, γ₀ z = γ₁ z) ∧
      T '' simp (τ₀ ∪ τ₁) =
        {x : Pr (N - q - 1) q | x.1 = 0 ∧ x.2.1 ∈ F ∧ γ₀ x.2.1 ≤ x.2.2 ∧ x.2.2 ≤ γ₁ x.2.1} ∧
      T '' (⋃ w ∈ τ₁, simp ((τ₀ ∪ τ₁).erase w)) =
        {x : Pr (N - q - 1) q | x.1 = 0 ∧ x.2.1 ∈ F ∧ x.2.2 = γ₀ x.2.1} ∧
      T '' (⋃ w ∈ τ₀, simp ((τ₀ ∪ τ₁).erase w)) =
        {x : Pr (N - q - 1) q | x.1 = 0 ∧ x.2.1 ∈ F ∧ x.2.2 = γ₁ x.2.1}

/-! ## A simplex is a ball (A2 item 8) -/

/-- **A2 item 8** (`simplex_homeo_disc`): the simplex on `s` is homeomorphic to the closed ball
of dimension `s.card - 1`, taking the boundary `⋃_w simp (s.erase w)` onto the sphere. -/
def SimplexBallForm : Prop :=
  ∀ {N : ℕ} (s : Finset (E N)), s.Nonempty → AffineIndependent ℝ ((↑) : s → E N) →
    ∃ e : (simp s) ≃ₜ closedBall (0 : E (s.card - 1)) 1,
      ∀ x : (simp s), ((e x : E (s.card - 1)) ∈ sphere (0 : E (s.card - 1)) 1 ↔
        (x : E N) ∈ ⋃ v ∈ s, simp (s.erase v))

/-! ## A3: the corrected general position statement `G6a'` of §4.1 -/

/-- **A3, `G6a'`** (§4.1): general position for the frozen image set, with the collision
precondition `hcol` that makes the statement true (see §1.2(a) for the counterexample to the
uncorrected joint form). -/
def GPaForm (n : ℕ) : Prop :=
  ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] (fz : Finset ι) (y₀ : ι → E n)
    (Pairs : Finset (Finset ι × Finset ι)) (Fixed : Finset (Finset (E n))),
    (∀ pr ∈ Pairs, ∃ v ∈ pr.1, v ∉ fz) →
    (∀ pr ∈ Pairs, pr.1.card ≤ n + 1) →
    (∀ pr ∈ Pairs, AffineIndependent ℝ (fun v : ↥(pr.1 ∩ fz) => y₀ v.val)) →
    (∀ pr ∈ Pairs, AffineIndependent ℝ (fun v : ↥(pr.2 ∩ fz) => y₀ v.val)) →
    (∀ pr ∈ Pairs, (∃ v ∈ pr.1 ∩ pr.2, v ∉ fz) →
      hullOf y₀ (pr.1 ∩ fz) ∩ hullOf y₀ (pr.2 ∩ fz) ⊆ hullOf y₀ (pr.1 ∩ pr.2 ∩ fz)) →
    ∀ (ε : ℝ), 0 < ε →
    ∃ y : ι → E n, (∀ i, dist (y i) (y₀ i) < ε) ∧ (∀ i ∈ fz, y i = y₀ i) ∧
      (∀ pr ∈ Pairs, AffineIndependent ℝ (fun v : ↥pr.1 => y v.val)) ∧
      (∀ pr ∈ Pairs, ∃ D : Set (E n), DomDim D ((pr.1.card : ℤ) + pr.2.card - 2 - n) ∧
          hullOf y pr.1 ∩ hullOf y pr.2 ⊆
            hullOf y (pr.1 ∩ pr.2) ∪ (hullOf y (pr.1 ∩ fz) ∩ hullOf y (pr.2 ∩ fz)) ∪ D) ∧
      (∀ pr ∈ Pairs, ∀ S ∈ Fixed, ∃ D : Set (E n), DomDim D ((pr.1.card : ℤ) + S.card - 2 - n) ∧
          hullOf y pr.1 ∩ simp S ⊆ hullOf y (pr.1 ∩ fz) ∪ D)

/-! ## A2 + A4: subdivision and shelling -/

/-- **A5, blueprint `G5`** (frozen variant) in the exact form E4 consumes (§7.2). -/
def PlApproxFrozenForm' (S : SubdivTools N) (n : ℕ) : Prop := PlApproxFrozenForm S n


/-- **(A5, new form)** frozen PL approximation **at a given level `r`** of the subdivision; the
frozen set `L` is a union of faces of the *fine* complex `S.sdIter r K` (lead's
`NOTES_LEAD_poincare_E4fix.md`, item 1).  Needed by the `E4` repair because `Tools.plApprox` can
only be applied once, at level `0`. -/
def PlApproxFrozenAtForm (S : SubdivTools N) (n : ℕ) : Prop :=
  ∀ (K : Cx N) (hK : K.faces.Finite) (r : ℕ) (L : Set (E N)), IsSubSp (S.sdIter r K hK) L →
    ∀ (f : E N → E n), ContinuousOn f K.space → ∀ (α β : ℝ), 0 < α → α < β → β < 1 →
    ∀ ε > 0,
    (∀ s ∈ (S.sdIter r K hK).faces, simp s ⊆ L → (∃ x ∈ simp s, f x ∈ closedCube β) →
        ∃ A : E N →ᵃ[ℝ] E n, EqOn f A (simp s)) →
    (∀ s ∈ (S.sdIter r K hK).faces, ∀ x ∈ simp s, ∀ y ∈ simp s,
        dist (f x) (f y) < min ε ((β - α) / 24)) →
    ∃ g : E N → E n, ContinuousOn g K.space ∧
      (∀ x ∈ K.space, dist (g x) (f x) < ε) ∧ EqOn g f L ∧
      (∀ x ∈ K.space, f x ∉ closedCube β → g x = f x) ∧
      ∀ s ∈ (S.sdIter r K hK).faces, (∃ x ∈ simp s, g x ∈ closedCube α) →
        ∃ A : E N →ᵃ[ℝ] E n, EqOn g A (simp s)

/-- **(A2, new form)** fullness: after at least one subdivision, the vertices of a face lying in a
subcomplex span a face inside the subcomplex (lead's `NOTES_LEAD_poincare_E4fix.md`, item 1). -/
def SdFullForm (S : SubdivTools N) : Prop :=
  ∀ r (K : Cx N) (hK : K.faces.Finite) (L : Set (E N)), IsSubSp K L → 1 ≤ r →
    ∀ s ∈ (S.sdIter r K hK).faces, ∀ t ⊆ s, t.Nonempty → (↑t : Set (E N)) ⊆ L → simp t ⊆ L

/-! ## A7: extending a homeomorphism of an open subspace -/

/-- **A7, blueprint `C0`** (`ext_homeo_open`). -/
def ExtHomeoOpenForm : Prop :=
  ∀ {M : Type u} [TopologicalSpace M] [T2Space M] (O : Set M), IsOpen O →
    (h : ↥O ≃ₜ ↥O) → ∀ C : Set ↥O, IsCompact C → (∀ x, x ∉ C → h x = x) →
    ∃ H : M ≃ₜ M, (∀ x : ↥O, H x = h x) ∧ ∀ x, x ∉ O → H x = x

/-! ## The bundle -/

/-- All the forms area A9 consumes, bundled.  `N` is the ambient dimension and `n` the
dimension of `M`. -/
structure Tools (N n : ℕ) where
  /-- A2 + A4: subdivision and shelling (`G3`, `G4`) -/
  subdiv : SubdivTools N
  /-- **Carrier property** of the subdivision (A2): a face of a subdivided complex that lies
  inside a subcomplex `L` is contained in a face of `K` that lies inside `L`.  For the
  barycentric subdivision this holds because the vertices of a face of `sdIter r K` are
  barycentres of faces of `K` inside a common carrier face.  It is what lets `E4`/`E5` replace
  a fine frozen face by a coarse one when applying `SmoothChart`. -/
  carrier : ∀ r (K : Cx N) (hK : K.faces.Finite) (L : Set (E N)), IsSubSp K L →
    ∀ s' ∈ (subdiv.sdIter r K hK).faces, simp s' ⊆ L →
      ∃ s ∈ K.faces, simp s' ⊆ simp s ∧ simp s ⊆ L
  /-- A5: frozen PL approximation (`G5`) -/
  plApprox : PlApproxFrozenForm subdiv n
  /-- A5: frozen PL approximation at a given subdivision level (E4 repair) -/
  plApproxAt : PlApproxFrozenAtForm subdiv n
  /-- A2: fullness of the subdivision (E4 repair) -/
  full : SdFullForm subdiv
  /-- A5: vertex perturbation (§7.2) -/
  vertexPerturb : VertexPerturbForm N n
  /-- A1: the prism push (`G1`) -/
  prismPush : PrismPushForm
  /-- A1: the relative prism push (`G1'`, Newman Thm 2) -/
  prismPushRel : PrismPushRelForm
  /-- A1: the join simplex is a prism (`G2`) -/
  joinPrism : JoinPrismForm N
  /-- A2 item 8: a simplex is a ball -/
  simplexBall : SimplexBallForm
  /-- A3: general position for frozen vertices (`G6a'`) -/
  gp : GPaForm.{u} n
  /-- A7: extending a homeomorphism of an open subspace (`C0`) -/
  extHomeo : ExtHomeoOpenForm.{u}

/-- The forms for every ambient dimension `N` (A9 works in a fixed `E N` with room, and
`engulf` uses `N = 2p + 4`). -/
def ToolsAll (n : ℕ) : Type := ∀ N : ℕ, Tools.{u} N n

end Work.Engulf
