import Mathlib
import Submission.Work.ATOM.ZS.Topo.Defs

/-!
# AREA ATOM / `ℤ[S]`: continuity of `β`

`β : (ℕ∪{∞}) × S ⟶ S` is `(j,x) ↦ e_{n(j)-1} x` (`s₀` when `n(j) = 0`), `(∞,x) ↦ x`.

Since `S` is the limit of its finite components, `β` is continuous as soon as each composite
`p ↦ π_m (β p)` with the projection to the `m`-th component is locally constant (that component
being discrete).  We prove this pointwise.  The relevant facts are

* for `n(j) ≥ m+1` we have `π_m (e_{n(j)-1} x) = π_m x`: the projections of `S` are compatible with
  the transition maps (`π_m ∘ σ_{n(j)-1} = leg (n(j)-1) m =` transition map), and
* for `n(j) < m+1` there are only finitely many such `j` (`Work.ATOM.levelData_finite_level_lt`),
  and for each of them `π_m (β(j,·))` depends on `x` only through `π_{n(j)-1} x` — hence
  `π_m ∘ β` is locally constant on the clopen slice `{j} × S`.

At the remaining point `(∞,x)`, `π_m ∘ β` is even *constant* on the clopen set
`({∞} ∪ {j | n(j) ≥ m+1}) × (π_m⁻¹{π_m x})`.

`β` is then `S.asLimit.lift` of the cone of these locally constant maps, and the lift is identified
with the explicit underlying function `Work.ATOM.betaFun` by separating points with the
projections.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open OnePoint

noncomputable section

namespace Work.ATOM.ZS.Topo

variable (S : LightProfinite.{0}) [Infinite S]

/-! ## Elementary topological inputs -/

/-- The fibre of a projection `π_k : S ⟶ S_k` is open (the target is discrete). -/
lemma isOpen_proj_fibre (k : ℕ) (x : ↥S) :
    IsOpen {z : ↥S | S.proj k z = S.proj k x} := by
  have h : {z : ↥S | S.proj k z = S.proj k x} = (S.proj k) ⁻¹' {S.proj k x} := rfl
  rw [h]
  exact (isOpen_discrete {S.proj k x}).preimage (ConcreteCategory.hom (S.proj k)).continuous

/-- The singleton `{j}` is open in `ℕ∪{∞}` (`Work.ATOM.isClopen_singleton_some`). -/
lemma isOpen_singleton_coe (j : ℕ) :
    IsOpen {q' : ↥(ℕ∪{∞}) | q' = (((j : ℕ) : ℕ∪{∞}))} := by
  rw [show {q' : ↥(ℕ∪{∞}) | q' = (((j : ℕ) : ℕ∪{∞}))} = {(OnePoint.some j)} by
    ext q; simp]
  exact (Work.ATOM.isClopen_singleton_some j).2

/-! ## Pointwise values of `β` -/

/-- `β` at a finite index, as a function of the second coordinate. -/
lemma betaFun_pair_eq {j : ℕ} (a : ↥(ℕ∪{∞})) (ha : a = (((j : ℕ) : ℕ∪{∞}))) (y : ↥S) :
    Work.ATOM.betaFun S ((a, y) : ↥(Work.ATOM.NS S)) =
      (if Work.ATOM.lvl S j = 0 then (Work.ATOM.levelData S).s₀
        else Work.ATOM.e S (Work.ATOM.lvl S j - 1) y) := by
  rw [ha, Work.ATOM.betaFun_lvl]

/-- On the slice `{j} × S` with `n(j) = 0`, `β` is constantly `s₀`. -/
lemma betaFun_pair_const_of_lvl_zero {j : ℕ} (hj : Work.ATOM.lvl S j = 0)
    (a : ↥(ℕ∪{∞})) (ha : a = (((j : ℕ) : ℕ∪{∞}))) (y : ↥S) :
    Work.ATOM.betaFun S ((a, y) : ↥(Work.ATOM.NS S)) = (Work.ATOM.levelData S).s₀ := by
  rw [betaFun_pair_eq S a ha y, if_pos hj]

/-- For `n(j) ≥ m+1`, the `m`-th projection of `β(j,y)` is `π_m y`. -/
lemma proj_betaFun_le (j m : ℕ) (h : m + 1 ≤ Work.ATOM.lvl S j) (y : ↥S) :
    S.proj m (Work.ATOM.betaFun S ((((j : ℕ) : ℕ∪{∞})), y)) = S.proj m y := by
  rw [Work.ATOM.betaFun_lvl, if_neg (by omega)]
  rw [Work.ATOM.e_apply, Work.ATOM.proj_sig_apply,
    Work.ATOM.leg_of_le S (Work.ATOM.lvl S j - 1) m (by omega)]
  exact congrFun (S.proj_comp_transitionMapLE' (n := m) (m := Work.ATOM.lvl S j - 1) (by omega)) y

/-- On the slice `{j} × S`, `π_m ∘ β` only depends on `π_{n(j)-1}`. -/
lemma betaFun_pair_proj_congr (j m : ℕ) (a : ↥(ℕ∪{∞})) (ha : a = (((j : ℕ) : ℕ∪{∞})))
    {y z : ↥S} (hz : S.proj (Work.ATOM.lvl S j - 1) y = S.proj (Work.ATOM.lvl S j - 1) z) :
    S.proj m (Work.ATOM.betaFun S ((a, y) : ↥(Work.ATOM.NS S))) =
      S.proj m (Work.ATOM.betaFun S ((((j : ℕ) : ℕ∪{∞}), z) : ↥(Work.ATOM.NS S))) := by
  rw [ha, Work.ATOM.betaFun_lvl, Work.ATOM.betaFun_lvl]
  by_cases h0 : Work.ATOM.lvl S j = 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0, Work.ATOM.e_apply, Work.ATOM.e_apply, hz]

/-! ## `n(j) → ∞` in the topology of `ℕ∪{∞}` -/

/-- The set of finite indices of level at least `N`, together with `∞`, is open in `ℕ∪{∞}`;
equivalently (`Work.ATOM.levelData_finite_level_lt`) its complement is finite. -/
lemma isOpen_level_ge (N : ℕ) :
    IsOpen {q : OnePoint ℕ | q = ∞ ∨ ∃ j : ℕ, q = (((j : ℕ) : ℕ∪{∞})) ∧
      N ≤ Work.ATOM.lvl S j} := by
  have h : {q : OnePoint ℕ | q = ∞ ∨ ∃ j : ℕ, q = (((j : ℕ) : ℕ∪{∞})) ∧
      N ≤ Work.ATOM.lvl S j}ᶜ =
      (((fun j : ℕ => (((j : ℕ) : ℕ∪{∞}))) '' {j : ℕ | Work.ATOM.lvl S j < N}) :
        Set (OnePoint ℕ)) := by
    ext q
    constructor
    · intro hq
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hq
      have hne : q ≠ ∞ := fun h => hq (Or.inl h)
      obtain ⟨j, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hne
      refine ⟨j, ?_, rfl⟩
      by_contra hlt
      exact hq (Or.inr ⟨j, rfl, Nat.le_of_not_lt hlt⟩)
    · rintro ⟨j, hj, rfl⟩
      simp only [Set.mem_setOf_eq] at hj
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
      rintro (h | ⟨j', he, hle⟩)
      · exact OnePoint.coe_ne_infty j h
      · rw [OnePoint.coe_eq_coe] at he
        rw [← he] at hle
        omega
  have hJc : IsClosed {q : OnePoint ℕ | q = ∞ ∨ ∃ j : ℕ, q = (((j : ℕ) : ℕ∪{∞})) ∧
      N ≤ Work.ATOM.lvl S j}ᶜ := by
    rw [h]
    exact ((Work.ATOM.levelData_finite_level_lt (S := S) N).image _).isClosed
  simpa using hJc.isOpen_compl

/-! ## Local constancy of the components of `β` -/

/-- The `m`-th component of `β` is locally constant. -/
lemma betaLeg_locallyConstant (m : ℕ) :
    IsLocallyConstant (fun p : ↥(Work.ATOM.NS S) => S.proj m (Work.ATOM.betaFun S p)) := by
  rw [IsLocallyConstant.iff_exists_open]
  rintro ⟨q, x⟩
  by_cases hq : q = ∞
  · subst hq
    refine ⟨{q' : ↥(ℕ∪{∞}) | q' = ∞ ∨ ∃ j : ℕ, q' = (((j : ℕ) : ℕ∪{∞})) ∧
        m + 1 ≤ Work.ATOM.lvl S j} ×ˢ {y : ↥S | S.proj m y = S.proj m x}, ?_,
      ⟨Or.inl rfl, rfl⟩, ?_⟩
    · exact (isOpen_level_ge S (m + 1)).prod (isOpen_proj_fibre S m x)
    · rintro ⟨q', z⟩ ⟨hq', hz⟩
      rcases hq' with rfl | ⟨j, rfl, hj⟩
      · simp only [Set.mem_setOf_eq] at hz
        rw [Work.ATOM.betaFun_infty, Work.ATOM.betaFun_infty]
        exact hz
      · rw [proj_betaFun_le S j m hj z, hz, Work.ATOM.betaFun_infty]
  · obtain ⟨j, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hq
    by_cases hk : Work.ATOM.lvl S j = 0
    · refine ⟨{q' : ↥(ℕ∪{∞}) | q' = (((j : ℕ) : ℕ∪{∞}))} ×ˢ (Set.univ : Set ↥S), ?_,
        ⟨rfl, Set.mem_univ x⟩, ?_⟩
      · exact (isOpen_singleton_coe j).prod isOpen_univ
      · rintro ⟨q', z⟩ ⟨hq', -⟩
        simp only [Set.mem_setOf_eq] at hq'
        rw [betaFun_pair_const_of_lvl_zero S hk q' hq' z,
          betaFun_pair_const_of_lvl_zero S hk ((((j : ℕ) : ℕ∪{∞}))) rfl x]
    · refine ⟨{q' : ↥(ℕ∪{∞}) | q' = (((j : ℕ) : ℕ∪{∞}))} ×ˢ
        {y : ↥S | S.proj (Work.ATOM.lvl S j - 1) y = S.proj (Work.ATOM.lvl S j - 1) x}, ?_,
        ⟨rfl, rfl⟩, ?_⟩
      · exact (isOpen_singleton_coe j).prod
          (isOpen_proj_fibre S (Work.ATOM.lvl S j - 1) x)
      · rintro ⟨q', z⟩ ⟨hq', hz⟩
        simp only [Set.mem_setOf_eq] at hq' hz
        exact betaFun_pair_proj_congr S j m q' hq' hz

/-! ## `β` as a morphism of light profinite sets -/

/-- The `m`-th leg of the cone defining `β`. -/
def betaLeg (m : ℕ) : Work.ATOM.NS S ⟶ S.component m :=
  ConcreteCategory.ofHom ⟨fun p => S.proj m (Work.ATOM.betaFun S p),
    (betaLeg_locallyConstant S m).continuous⟩

@[simp] lemma betaLeg_apply (m : ℕ) (p : ↥(Work.ATOM.NS S)) :
    (betaLeg S m) p = S.proj m (Work.ATOM.betaFun S p) := rfl

/-- The cone condition for the legs. -/
lemma betaLeg_naturality (m : ℕ) :
    betaLeg S (m + 1) ≫ S.transitionMap m = betaLeg S m := by
  ext p
  simp only [ConcreteCategory.comp_apply, betaLeg_apply]
  show S.transitionMap m (S.proj (m + 1) (Work.ATOM.betaFun S p)) =
    S.proj m (Work.ATOM.betaFun S p)
  exact congrFun (S.proj_comp_transitionMap' m) (Work.ATOM.betaFun S p)

/-- The cone over `S.diagram` whose point is `(ℕ∪{∞}) × S` and whose legs are the components
of `β`. -/
def betaCone : Cone S.diagram where
  pt := Work.ATOM.NS S
  π := NatTrans.ofOpSequence (fun m => betaLeg S m) (fun m => (betaLeg_naturality S m).symm)

/-- The legs of `betaCone`. -/
@[simp] lemma betaCone_π_app (m : ℕ) :
    (betaCone S).π.app (Opposite.op m) = betaLeg S m := rfl

/-- `β`, as a morphism of light profinite sets. -/
def betaMap : Work.ATOM.NS S ⟶ S := S.asLimit.lift (betaCone S)

/-- The defining property of `betaMap`: its `m`-th component is `π_m ∘ β`. -/
lemma proj_betaMap (m : ℕ) (p : ↥(Work.ATOM.NS S)) :
    S.proj m (betaMap S p) = S.proj m (Work.ATOM.betaFun S p) := by
  rw [← ConcreteCategory.comp_apply (f := betaMap S) (g := S.proj m) (x := p)]
  have h : (betaMap S ≫ S.proj m) = betaLeg S m := by
    show (S.asLimit.lift (betaCone S) ≫ S.asLimitCone.π.app (Opposite.op m)) = betaLeg S m
    rw [S.asLimit.fac (betaCone S) (Opposite.op m)]
    rfl
  exact congrArg (fun f : Work.ATOM.NS S ⟶ S.component m => (ConcreteCategory.hom f) p) h

/-! ## Identifying the underlying function of `betaMap` -/

/-- The projections `π_m : S ⟶ S_m` separate the points of `S`. -/
lemma eq_of_forall_proj_eq {y z : ↥S} (h : ∀ m, S.proj m y = S.proj m z) : y = z := by
  have hpt : (Work.ATOM.ptAt y : Work.ATOM.pt ⟶ S) = Work.ATOM.ptAt z := by
    apply S.asLimit.hom_ext
    intro m
    ext u
    simp only [ConcreteCategory.comp_apply, Work.ATOM.ptAt, ConcreteCategory.hom_ofHom]
    exact h m.unop
  have h2 := congrArg
    (fun φ : Work.ATOM.pt ⟶ S => (ConcreteCategory.hom φ) PUnit.unit) hpt
  simpa [Work.ATOM.ptAt] using h2

/-- The underlying function of `betaMap` is `β`. -/
lemma betaMap_apply (p : ↥(Work.ATOM.NS S)) : betaMap S p = Work.ATOM.betaFun S p :=
  eq_of_forall_proj_eq S fun m => proj_betaMap S m p

/-- Continuity of `β : (ℕ∪{∞}) × S ⟶ S` (`Work.ATOM.betaFun`): `(j,x) ↦ e_{n(j)-1} x` (`s₀` when
`n(j) = 0`), `(∞,x) ↦ x`.  Route: as for `ẽ`, build `S.asLimit.lift` of the cone of the locally
constant maps `p ↦ proj m (β p)`; the key input is `n(j) → ∞` (`Work.ATOM.levelData_finite_level`,
`Work.ATOM.levelData_finite_level_lt`) together with the leg lemmas of
`Submission/Work/ATOM/ZS/Level.lean`. -/
theorem betaFun_continuous (S : LightProfinite.{0}) [Infinite S] :
    Continuous (Work.ATOM.betaFun S) := by
  have h : Work.ATOM.betaFun S = ⇑(ConcreteCategory.hom (betaMap S)) :=
    funext fun p => (betaMap_apply S p).symm
  rw [h]
  exact (ConcreteCategory.hom (betaMap S)).continuous

end Work.ATOM.ZS.Topo
