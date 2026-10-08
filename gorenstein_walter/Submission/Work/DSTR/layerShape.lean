import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.ASM.oddCore_odd
import Submission.Work.DSTR.layerShapeAux.exists_surj_range_center
import Submission.Work.DSTR.layerShapeAux.isQuasisimple_inf_oddCore_le_center

/-!
# DS7: the shape of the layer (`Work.GW2.LayerShapeProp`)

`E/Z(E)` of a normal quasisimple subgroup `E` of a D-group `X` is `A₇` or `L₂(q)`, `q ≥ 5`.

The proof descends the normal quasisimple subgroup `E` to the quotient `Q = X/O(X)`: the image
`Ē = EO(X)/O(X)` is normal in `Q` (it is not trivial since `E ⊄ O(X)`), and `E/Z(E)` is a quotient
of `Ē` by a *central* subgroup (`E ∩ O(X) ≤ Z(E)`).  Since `X` is a D-group, `Q` has one of the
four `Work.GW2.DShape` shapes, and the case analysis on `Q` gives the conclusion:

* `Q` a 2-group: `Ē` is a 2-group, hence solvable, so `E/Z(E)` would be solvable — impossible for a
  quasisimple `E`;
* `Q` with a normal self-centralizing four-group: `Q` is solvable, same contradiction;
* `Q ≅ A₇`: `Ē` is a nontrivial normal subgroup, so `Ē = Q` and `E/Z(E) ≅ A₇`;
* `Q` has a normal `L` of odd index with `L ≅ PSL(2,q)` or `L ≅ PGL(2,q)`: `Ē ∩ L` is non-trivial
  (otherwise `Ē` would be odd, hence solvable) and surjects onto `E/Z(E)`, and simplicity of `L`
  (resp. of the normal `PSL(2,q) ⊆ PGL(2,q)`) identifies `E/Z(E)` with `PSL(2,q)`.
-/

open scoped MatrixGroups commutatorElement

set_option linter.style.haveILetI false

namespace Work.DSTR

open Subgroup

/-! ## Elementary helpers -/

section Helpers

variable {G : Type*} [Group G]

/-- `⁅E,E⁆ = E` (as subgroups of the ambient group) says that `↥E` is perfect. -/
lemma commutator_top_of_commutator_eq_self {E : Subgroup G} (h : ⁅E, E⁆ = E) :
    commutator ↥E = ⊤ := by
  have htop : Subgroup.map E.subtype (⊤ : Subgroup ↥E) = E := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
      exact y.2
    · intro hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  have hmap : Subgroup.map E.subtype (commutator ↥E) =
      Subgroup.map E.subtype (⊤ : Subgroup ↥E) := by
    show Subgroup.map E.subtype ⁅(⊤ : Subgroup ↥E), ⊤⁆ = _
    rw [Subgroup.map_commutator, htop, h]
  exact Subgroup.map_injective E.subtype_injective hmap

end Helpers

/-- Simplicity transports along a multiplicative equivalence. -/
lemma isSimpleGroup_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    [IsSimpleGroup G] : IsSimpleGroup H := by
  haveI : Nontrivial H := e.symm.surjective.nontrivial
  refine IsSimpleGroup.mk fun N hN => ?_
  rcases Subgroup.Normal.eq_bot_or_eq_top (N.comap e.toMonoidHom) with h | h
  · left
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : e.symm x ∈ N.comap e.toMonoidHom := by
      rw [Subgroup.mem_comap]; simpa using hx
    rw [h, Subgroup.mem_bot] at hx'
    exact e.symm.injective (by rw [hx', map_one])
  · right
    refine le_antisymm le_top ?_
    intro x _
    have hx' : e.symm x ∈ N.comap e.toMonoidHom := by
      rw [h]; exact Subgroup.mem_top _
    rw [Subgroup.mem_comap] at hx'
    simpa using hx'

/-- A surjective homomorphism from a simple group onto a nontrivial group is an isomorphism. -/
lemma mulEquiv_of_surjective_of_isSimpleGroup {G H : Type*} [Group G] [Group H] [IsSimpleGroup G]
    [Nontrivial H] (g : G →* H) (hg : Function.Surjective g) : Nonempty (G ≃* H) := by
  have hker : g.ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top g.ker with h | h
    · exact h
    · exfalso
      have hone : ∀ x : G, g x = 1 := fun x => MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x)
      have hsub : Subsingleton H := ⟨fun y y' => by
        obtain ⟨x, rfl⟩ := hg y
        obtain ⟨x', rfl⟩ := hg y'
        rw [hone x, hone x']⟩
      obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial H).exists_pair_ne
      exact hab (hsub.elim a b)
  exact ⟨MulEquiv.ofBijective g ⟨(MonoidHom.ker_eq_bot_iff g).mp hker, hg⟩⟩

/-- The quotient by a normal subgroup containing all commutators is commutative. -/
lemma isMulCommutative_quotient_of_commutator_le {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (h : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ N) : IsMulCommutative (G ⧸ N) := by
  refine IsMulCommutative.of_comm fun x y => ?_
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N y
  have hab : (⁅a, b⁆ : G) ∈ N :=
    h (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b))
  have h1 : (QuotientGroup.mk' N ⁅a, b⁆ : G ⧸ N) = 1 := by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']; exact hab
  rw [map_commutatorElement] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

section Coercions

variable {Q : Type*} [Group Q]

/-- The underlying element of `Subgroup.inclusion h x` is `x`. -/
@[simp] lemma inclusion_coe {H K : Subgroup Q} (h : H ≤ K) (x : ↥H) :
    ((Subgroup.inclusion h x : ↥K) : Q) = (x : Q) := rfl

/-- Membership in `H.subgroupOf K` for an element of `K` whose underlying element lies in `H`. -/
lemma mem_subgroupOf_of_le {H K : Subgroup Q} (h : H ≤ K) {x : Q} (hx : x ∈ H) :
    (⟨x, h hx⟩ : ↥K) ∈ H.subgroupOf K := by
  rw [Subgroup.mem_subgroupOf]; exact hx

/-- Conjugation by an element of `L` stays inside a subgroup of `L` normal in `L`. -/
lemma conj_mem_of_subgroupOf_normal {M L : Subgroup Q} (hn : (M.subgroupOf L).Normal) (hML : M ≤ L)
    {x y : Q} (hx : x ∈ M) (hy : y ∈ L) : y * x * y⁻¹ ∈ M := by
  have h1 := hn.conj_mem (⟨x, hML hx⟩ : ↥L) (mem_subgroupOf_of_le hML hx) (⟨y, hy⟩ : ↥L)
  rw [Subgroup.mem_subgroupOf] at h1
  simpa using h1

end Coercions

/-- A quasisimple subgroup is nontrivial. -/
lemma nontrivial_of_isQuasisimple {X : Type*} [Group X] {E : Subgroup X}
    (hEq : Work.GW2.IsQuasisimple E) : Nontrivial ↥E := by
  haveI : IsSimpleGroup (↥E ⧸ Subgroup.center ↥E) := hEq.2
  exact (QuotientGroup.mk'_surjective (Subgroup.center ↥E)).nontrivial

/-- A quasisimple subgroup is not contained in the odd core. -/
lemma not_le_oddCore_of_isQuasisimple {X : Type*} [Group X] [Finite X]
    (hFT : Work.GW2.FeitThompsonProp) {E : Subgroup X} (hEq : Work.GW2.IsQuasisimple E) :
    ¬ E ≤ Work.GW2.oddCore X := by
  intro hle
  have hodd : Odd (Nat.card ↥E) :=
    Odd.of_dvd_nat (Work.ASM.oddCore_odd X) (Subgroup.card_dvd_of_le hle)
  haveI : Group.IsSolvable ↥E :=
    Work.DSTR.layerShapeAux.isSolvable_of_odd_of_feitThompson hFT hodd
  haveI : Nontrivial ↥E := nontrivial_of_isQuasisimple hEq
  have hperf : commutator ↥E = ⊤ := commutator_top_of_commutator_eq_self hEq.1
  have hlt : commutator ↥E < ⊤ := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥E
  rw [hperf] at hlt
  exact absurd hlt (lt_irrefl _)

/-- For quasisimple `E`, the group `E ⧸ Z(E)` is not solvable. -/
lemma not_isSolvable_quotient_center {X : Type*} [Group X] {E : Subgroup X}
    (hEq : Work.GW2.IsQuasisimple E) :
    ¬ Group.IsSolvable (↥E ⧸ Subgroup.center ↥E) := by
  intro hs
  haveI := hs
  haveI : IsSimpleGroup (↥E ⧸ Subgroup.center ↥E) := hEq.2
  haveI : Nontrivial ↥E := nontrivial_of_isQuasisimple hEq
  haveI : Group.IsSolvable ↥E :=
    Group.isSolvable_of_subgroup_quotient (Subgroup.center ↥E)
  have hperf : commutator ↥E = ⊤ := commutator_top_of_commutator_eq_self hEq.1
  have hlt : commutator ↥E < ⊤ := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥E
  rw [hperf] at hlt
  exact absurd hlt (lt_irrefl _)

/-- The automorphism group of a Klein four-group is solvable (it embeds into `Perm (Fin 3)`). -/
lemma isSolvable_mulAut_of_isFourGroup {Q : Type*} [Group Q] (V : Subgroup Q)
    (hV : Work.GW2.IsFourGroup V) : Group.IsSolvable (MulAut ↥V) := by
  classical
  have hcard : Nat.card ↥V = 4 := hV.1
  haveI : Finite ↥V := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  letI : Fintype ↥V := Fintype.ofFinite ↥V
  -- restriction of an automorphism to the three nonidentity elements
  let f : MulAut ↥V →* Equiv.Perm {v : ↥V // v ≠ 1} :=
    { toFun := fun e =>
        { toFun := fun v => ⟨e v.1, fun h => v.2 (e.injective (by rw [h, map_one]))⟩
          invFun := fun v => ⟨e.symm v.1, fun h => v.2 (e.symm.injective (by rw [h, map_one]))⟩
          left_inv := fun v => by ext; simp
          right_inv := fun v => by ext; simp }
      map_one' := by ext v; rfl
      map_mul' := fun e e' => by ext v; rfl }
  have hf : Function.Injective f := by
    intro e e' h
    ext v
    by_cases hv : v = 1
    · subst hv; rw [map_one, map_one]
    · have h2 := congrArg (fun g : Equiv.Perm {w : ↥V // w ≠ 1} => (g ⟨v, hv⟩ : ↥V)) h
      simpa [f] using h2
  have hcard3 : Fintype.card {v : ↥V // v ≠ 1} = 3 := by
    have h4 : Fintype.card ↥V = 4 := by rw [← Nat.card_eq_fintype_card]; exact hcard
    rw [Fintype.card_subtype_compl (fun v : ↥V => v = 1), Fintype.card_subtype_eq (1 : ↥V)]
    omega
  haveI : IsZGroup (Equiv.Perm (Fin 3)) :=
    IsZGroup.of_squarefree (by
      have hcard6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
        decide
      rw [hcard6]
      rw [Nat.squarefree_iff_prime_squarefree]
      intro p hp hdvd
      have hle : p * p ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
      have hge : 2 ≤ p := hp.two_le
      have : p ≤ 2 := by nlinarith
      interval_cases p
      norm_num at hdvd)
  haveI : Group.IsSolvable (Equiv.Perm {v : ↥V // v ≠ 1}) := by
    have : IsZGroup (Equiv.Perm {v : ↥V // v ≠ 1}) :=
      IsZGroup.of_injective
        (f := (Equiv.permCongrHom (Fintype.equivFinOfCardEq hcard3)).toMonoidHom)
        (Equiv.permCongrHom _).injective
    exact inferInstance
  exact Group.isSolvable_of_isSolvable_injective (f := f) hf

/-- A finite group with a normal self-centralizing Klein four-subgroup is solvable. -/
lemma isSolvable_of_normal_fourGroup_selfCentralizing {Q : Type*} [Group Q] [Finite Q]
    (V : Subgroup Q) (hVn : V.Normal) (hV : Work.GW2.IsFourGroup V)
    (hc : Subgroup.centralizer (V : Set Q) = V) : Group.IsSolvable Q := by
  haveI := hVn
  -- `V` is abelian (every element squares to one)
  haveI hVcomm : IsMulCommutative ↥V := by
    refine IsMulCommutative.of_comm fun a b => ?_
    have ha : a⁻¹ = a := by
      refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
      show (((a * a : ↥V)) : Q) = 1
      simpa [pow_two] using hV.2 (a : Q) a.2
    have hb : b⁻¹ = b := by
      refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
      show (((b * b : ↥V)) : Q) = 1
      simpa [pow_two] using hV.2 (b : Q) b.2
    have hab : (a * b)⁻¹ = a * b := by
      refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
      show ((((a * b) * (a * b) : ↥V)) : Q) = 1
      simpa [pow_two] using hV.2 ((a : Q) * (b : Q)) (V.mul_mem a.2 b.2)
    rw [← hab, mul_inv_rev, ha, hb]
  -- the kernel of the conjugation action is `C_Q(V) = V`
  have hker_le : (MulAut.conjNormal (H := V)).ker ≤ V := by
    intro q hq
    have h1 : MulAut.conjNormal (H := V) q = 1 := MonoidHom.mem_ker.mp hq
    rw [← hc, Subgroup.mem_centralizer_iff]
    intro v hv
    have h2 := congrArg (fun g : MulAut ↥V => ((g ⟨v, hv⟩ : ↥V) : Q)) h1
    simp only [MulAut.one_apply, MulAut.conjNormal_apply] at h2
    have h3 : q * v = v * q := by
      have h4 := congrArg (fun w : Q => w * q) h2
      simpa [mul_assoc] using h4
    exact h3.symm
  have hV_le_ker : V ≤ (MulAut.conjNormal (H := V)).ker := by
    intro v hv
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun h => ?_
    apply Subtype.ext
    rw [MulAut.one_apply, MulAut.conjNormal_apply]
    have h2 : (v : Q) * (h : Q) = (h : Q) * v := by
      have h3 := congrArg (fun w : ↥V => (w : Q)) (mul_comm' (⟨v, hv⟩ : ↥V) h)
      simpa using h3
    calc v * (h : Q) * v⁻¹ = (h : Q) * v * v⁻¹ := by rw [h2]
      _ = (h : Q) := by rw [mul_assoc, mul_inv_cancel, mul_one]
  -- `Q ⧸ V` embeds into `MulAut ↥V`, which is solvable
  have hinj : Function.Injective (QuotientGroup.lift V (MulAut.conjNormal (H := V)) hV_le_ker) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_lift, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
    exact hker_le
  haveI : Group.IsSolvable (MulAut ↥V) := isSolvable_mulAut_of_isFourGroup V hV
  haveI : Group.IsSolvable (Q ⧸ V) :=
    Group.isSolvable_of_isSolvable_injective
      (f := QuotientGroup.lift V (MulAut.conjNormal (H := V)) hV_le_ker) hinj
  exact Group.isSolvable_of_subgroup_quotient V

/-- Model fact: an overgroup `L` of an isomorphic copy of `PGL(2,q)` (`p` odd, `q = p ^ k ≥ 5`)
contains a normal subgroup isomorphic to `PSL(2,q)` which contains the commutators of `L`. -/
lemma exists_normal_psl_in_overgroup {Q : Type*} [Group Q] (L : Subgroup Q)
    (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    (e : ↥L ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)) :
    ∃ M : Subgroup Q, M ≤ L ∧ (M.subgroupOf L).Normal ∧ IsSimpleGroup ↥M ∧
      Nonempty (M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) ∧
      ⁅(⊤ : Subgroup ↥L), ⊤⁆ ≤ M.subgroupOf L := by
  classical
  have hk : k ≠ 0 := by rintro rfl; simp at hq
  have hcardF : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk
  haveI hPSLsimple : IsSimpleGroup
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hcardF]; omega)
  -- the image `M₀` of `SL(2,q)` in `PGL(2,q)`
  let M₀ : Subgroup (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)) :=
    (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := GaloisField p k)).range
  have hM₀_def : M₀ = (Matrix.SpecialLinearGroup.toPGL (n := Fin 2)
      (R := GaloisField p k)).range := rfl
  have hM₀_normal : M₀.Normal := by
    rw [hM₀_def, Matrix.SpecialLinearGroup.toPGL, MonoidHom.range_comp,
      Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    exact Subgroup.Normal.map (MonoidHom.normal_ker _) _ Matrix.ProjGenLinGroup.mk_surjective
  have hM₀_iso : M₀ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k) :=
    (QuotientGroup.quotientKerEquivRange
        (Matrix.SpecialLinearGroup.toPGL (n := Fin 2) (R := GaloisField p k))).symm.trans
      (QuotientGroup.quotientMulEquivOfEq
        (Matrix.SpecialLinearGroup.toPGL_ker (n := Fin 2) (R := GaloisField p k)))
  -- commutators of `PGL(2,q)` lie in `M₀`: determinants are trivial
  have hPGLcomm : ∀ u v : Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k), ⁅u, v⁆ ∈ M₀ := by
    intro u v
    obtain ⟨a, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective u
    obtain ⟨b, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective v
    rw [← map_commutatorElement (Matrix.ProjGenLinGroup.mk (n := Fin 2)
      (R := GaloisField p k)) a b]
    rw [hM₀_def, Matrix.SpecialLinearGroup.toPGL, MonoidHom.range_comp, Subgroup.mem_map]
    refine ⟨⁅a, b⁆, ?_, rfl⟩
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
    rw [map_commutatorElement (Matrix.GeneralLinearGroup.det (n := Fin 2)
      (R := GaloisField p k)) a b]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  -- transport to the abstract overgroup `L`
  let Ψ : Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k) →* Q :=
    L.subtype.comp e.symm.toMonoidHom
  have hΨ_inj : Function.Injective Ψ := fun a b h => e.symm.injective (Subtype.coe_injective h)
  refine ⟨M₀.map Ψ, ?_, ?_, ?_, ?_, ?_⟩
  · -- `M₀.map Ψ ≤ L`
    intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact (e.symm y).2
  · -- `M₀.map Ψ` is normal in `L`
    refine Subgroup.Normal.mk fun x hx y => ?_
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp hx
    have hxe : (e.symm m : ↥L) = x := by
      have h1 : ((e.symm m : ↥L) : Q) = (x : Q) := by
        rw [show ((e.symm m : ↥L) : Q) = Ψ m from rfl, hmx]
      exact Subtype.ext h1
    refine ⟨e y * m * (e y)⁻¹, hM₀_normal.conj_mem m hm (e y), ?_⟩
    have hsym : e.symm (e y * m * (e y)⁻¹) = y * x * y⁻¹ := by
      rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply, ← hxe]
    show ((e.symm (e y * m * (e y)⁻¹) : ↥L) : Q) = _
    rw [hsym]
  · -- simple
    exact isSimpleGroup_of_mulEquiv
      ((Subgroup.equivMapOfInjective M₀ Ψ hΨ_inj).symm.trans hM₀_iso).symm
  · -- isomorphic to `PSL(2,q)`
    exact ⟨(Subgroup.equivMapOfInjective M₀ Ψ hΨ_inj).symm.trans hM₀_iso⟩
  · -- commutators of `L` lie in `M₀.map Ψ`
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    refine ⟨e ⁅x, y⁆, ?_, ?_⟩
    · rw [map_commutatorElement]
      exact hPGLcomm (e x) (e y)
    · show ((e.symm (e ⁅x, y⁆) : ↥L) : Q) = _
      rw [MulEquiv.symm_apply_apply]

/-- **DS7** (`Work.GW2.LayerShapeProp`): `E/Z(E)` of a normal quasisimple subgroup of a D-group is `A_7` or `L_2(q)`, `q >= 5`.  The normal quasisimple subgroup descends to a normal subgroup of `X/O(X)`, whose `DShape` gives one of the four clauses. -/
theorem layerShape (h2 : Work.GW2.OddCoreQuotProp) (h5 : Work.GW2.LayerUniqueProp)
    (h6 : Work.GW2.QuasisimpleCenterOddProp) (hautL2 : Work.GW2.AutL2Prop)
    (hautA7 : Work.GW2.AutA7Prop) : Work.GW2.LayerShapeProp := by
  intro X instX instFX hFT hSyl hD E hEn hEq
  classical
  haveI hOn : (Work.GW2.oddCore X).Normal := Work.GW2.oddCore_normal X
  haveI hSsimple : IsSimpleGroup (↥E ⧸ Subgroup.center ↥E) := hEq.2
  have hSnsolv : ¬ Group.IsSolvable (↥E ⧸ Subgroup.center ↥E) := not_isSolvable_quotient_center hEq
  -- the quotient map and the image of `E`
  let π : X →* (X ⧸ Work.GW2.oddCore X) := QuotientGroup.mk' (Work.GW2.oddCore X)
  let φ : ↥E →* (X ⧸ Work.GW2.oddCore X) := π.comp E.subtype
  let Ebar : Subgroup (X ⧸ Work.GW2.oddCore X) := φ.range
  have hEbar_eq : Ebar = Subgroup.map π E := by
    have hφx : ∀ x : ↥E, φ x = π (x : X) := fun _ => rfl
    change φ.range = Subgroup.map π E
    rw [MonoidHom.range_eq_map]
    ext y
    constructor
    · rintro ⟨x, -, hx⟩
      rw [hφx x] at hx
      exact ⟨(x : X), x.2, hx⟩
    · rintro ⟨x, hx, hxy⟩
      refine ⟨⟨x, hx⟩, Subgroup.mem_top _, ?_⟩
      rw [hφx]
      exact hxy
  have hEbar_norm : Ebar.Normal :=
    hEbar_eq ▸ Subgroup.Normal.map hEn π (QuotientGroup.mk'_surjective _)
  have hEbar_ne_bot : Ebar ≠ ⊥ := by
    intro hbot
    refine not_le_oddCore_of_isQuasisimple hFT hEq ?_
    have h2 : Subgroup.map π E = ⊥ := by rw [← hEbar_eq]; exact hbot
    have h3 : E ≤ π.ker := (Subgroup.map_eq_bot_iff E).mp h2
    rwa [QuotientGroup.ker_mk'] at h3
  -- the kernel of `φ` is central in `E`, so `E/Z(E)` is a quotient of `Ē`
  have hφ_ker_le : φ.ker ≤ Subgroup.center ↥E := by
    intro x hx
    have hxO : (x : X) ∈ Work.GW2.oddCore X := by
      have h1 : φ x = 1 := MonoidHom.mem_ker.mp hx
      have h2 : QuotientGroup.mk' (Work.GW2.oddCore X) (x : X) = 1 := h1
      exact (QuotientGroup.eq_one_iff (x : X)).mp h2
    have hmem : (x : X) ∈ (Subgroup.center ↥E).map E.subtype :=
      Work.DSTR.layerShapeAux.isQuasisimple_inf_oddCore_le_center hFT hEq
        (Subgroup.mem_inf.mpr ⟨x.2, hxO⟩)
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hmem
    have hce : c = x := Subtype.ext hcx
    rw [← hce]; exact hc
  obtain ⟨f, hf_surj, _hf_ker, _hf_comp⟩ :=
    Work.DSTR.layerShapeAux.exists_surj_range_center φ hφ_ker_le
  -- the four shapes of `Q = X/O(X)`
  rcases hD with hpg | ⟨V, hVn, hV4, hVc⟩ | ⟨e7⟩ | ⟨L, hLn, hLodd, p, k, hp, hoddp, hq, hLiso⟩
  · -- `Q` is a 2-group
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI hpgE : IsPGroup 2 ↥Ebar :=
      IsPGroup.of_injective hpg Ebar.subtype Subtype.coe_injective
    haveI : Group.IsNilpotent ↥Ebar := hpgE.isNilpotent
    haveI : Group.IsSolvable ↥Ebar := inferInstance
    exact absurd (Group.isSolvable_of_surjective (f := f) hf_surj) hSnsolv
  · -- `Q` has a normal self-centralizing four-subgroup
    haveI : Group.IsSolvable (X ⧸ Work.GW2.oddCore X) :=
      isSolvable_of_normal_fourGroup_selfCentralizing V hVn hV4 hVc
    haveI : Group.IsSolvable ↥Ebar := inferInstance
    exact absurd (Group.isSolvable_of_surjective (f := f) hf_surj) hSnsolv
  · -- `Q ≅ A₇`
    obtain ⟨e7⟩ := e7
    haveI hA7 : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (α := Fin 7) (by simp)
    have himg_norm : (Ebar.map e7.toMonoidHom).Normal :=
      Subgroup.Normal.map hEbar_norm e7.toMonoidHom e7.surjective
    have himg : Ebar.map e7.toMonoidHom = ⊤ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top (Ebar.map e7.toMonoidHom) with h | h
      · exfalso
        refine hEbar_ne_bot (Subgroup.map_injective (f := e7.toMonoidHom) e7.injective ?_)
        rw [h, Subgroup.map_bot]
      · exact h
    have hEbar_iso : Nonempty (↥Ebar ≃* alternatingGroup (Fin 7)) := by
      refine ⟨?_⟩
      have h1 : ↥Ebar ≃* ↥(Ebar.map e7.toMonoidHom) := MulEquiv.subgroupMap e7 Ebar
      rw [himg] at h1
      exact h1.trans Subgroup.topEquiv
    obtain ⟨eE⟩ := hEbar_iso
    obtain ⟨eS⟩ := mulEquiv_of_surjective_of_isSimpleGroup (f.comp eE.symm.toMonoidHom)
      (hf_surj.comp eE.symm.surjective)
    exact Or.inl ⟨eS.symm⟩
  · -- `Q` has a normal `L` of odd index, `L ≅ PSL(2,q)` or `L ≅ PGL(2,q)`
    haveI : Fact p.Prime := hp
    haveI hLn' : L.Normal := hLn
    let K : Subgroup (X ⧸ Work.GW2.oddCore X) := Ebar ⊓ L
    have hKnorm : K.Normal := inferInstance
    have hKleEbar : K ≤ Ebar := inf_le_left
    have hKleL : K ≤ L := inf_le_right
    have hKnorm_Ebar : (K.subgroupOf Ebar).Normal := hKnorm.subgroupOf Ebar
    -- `Ē ⧸ K` is odd (it embeds into `Q ⧸ L`)
    have hodd_quot : Odd (Nat.card (↥Ebar ⧸ K.subgroupOf Ebar)) := by
      have hker : ((QuotientGroup.mk' L).comp Ebar.subtype).ker = K.subgroupOf Ebar := by
        ext x
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.mem_subgroupOf]
        show QuotientGroup.mk' L (x : X ⧸ Work.GW2.oddCore X) = 1 ↔
          (x : X ⧸ Work.GW2.oddCore X) ∈ Ebar ⊓ L
        rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_inf]
        exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
      have hcard1 : Nat.card (↥Ebar ⧸ K.subgroupOf Ebar) =
          Nat.card ↥(((QuotientGroup.mk' L).comp Ebar.subtype).range) := by
        rw [← hker]
        exact Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
      have hdvd : Nat.card ↥(((QuotientGroup.mk' L).comp Ebar.subtype).range) ∣
          Nat.card ↥(⊤ : Subgroup ((X ⧸ Work.GW2.oddCore X) ⧸ L)) :=
        Subgroup.card_dvd_of_le le_top
      have hodd_top : Odd (Nat.card ↥(⊤ : Subgroup ((X ⧸ Work.GW2.oddCore X) ⧸ L))) := by
        rw [Nat.card_congr (Subgroup.topEquiv (G := (X ⧸ Work.GW2.oddCore X) ⧸ L)).toEquiv,
          ← Subgroup.index_eq_card]
        exact hLodd
      rw [hcard1]
      exact Odd.of_dvd_nat hodd_top hdvd
    by_cases hKW : K.subgroupOf Ebar ≤ f.ker
    · -- `S` is a quotient of the odd-order group `Ē ⧸ K`
      haveI : Group.IsSolvable (↥Ebar ⧸ K.subgroupOf Ebar) :=
        Work.DSTR.layerShapeAux.isSolvable_of_odd_of_feitThompson hFT hodd_quot
      exact absurd (Group.isSolvable_of_surjective
          (f := QuotientGroup.lift (K.subgroupOf Ebar) f hKW)
          (QuotientGroup.lift_surjective_of_surjective _ f hf_surj hKW)) hSnsolv
    · -- `K` surjects onto `S`
      have hKne : K ≠ ⊥ := by
        intro hbot
        exact hKW (by rw [hbot, Subgroup.bot_subgroupOf]; exact bot_le)
      let g : ↥K →* (↥E ⧸ Subgroup.center ↥E) := f.comp (Subgroup.inclusion hKleEbar)
      have hg_range : g.range = Subgroup.map f (K.subgroupOf Ebar) := by
        ext y
        rw [MonoidHom.mem_range, Subgroup.mem_map]
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨Subgroup.inclusion hKleEbar x, x.2, rfl⟩
        · rintro ⟨z, hz, rfl⟩
          exact ⟨⟨(z : X ⧸ Work.GW2.oddCore X), hz⟩, by simp [g, Subgroup.inclusion]⟩
      have hg_normal : g.range.Normal :=
        hg_range ▸ Subgroup.Normal.map hKnorm_Ebar f hf_surj
      have hg_surj : Function.Surjective g := by
        rw [← MonoidHom.range_eq_top]
        rcases Subgroup.Normal.eq_bot_or_eq_top g.range with h | h
        · exfalso
          apply hKW
          intro x hx
          rw [MonoidHom.mem_ker]
          have hx' : g ⟨(x : X ⧸ Work.GW2.oddCore X), hx⟩ = 1 := by
            have hmem : g ⟨(x : X ⧸ Work.GW2.oddCore X), hx⟩ ∈ g.range :=
              MonoidHom.mem_range.mpr ⟨_, rfl⟩
            rwa [h, Subgroup.mem_bot] at hmem
          show f x = 1
          simpa [g, Subgroup.inclusion] using hx'
        · exact h
      rcases hLiso with hPSLis | hPGLis
      · -- `L ≅ PSL(2, q)`: `L` is simple, so `K = L` and `g` is injective
        obtain ⟨eL⟩ := hPSLis
        have hk : k ≠ 0 := by rintro rfl; simp at hq
        have hcardF : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk
        haveI hPSLsimple : IsSimpleGroup
            (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) :=
          Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hcardF]; omega)
        haveI hLsimple : IsSimpleGroup ↥L := isSimpleGroup_of_mulEquiv eL.symm
        have hKL : K = L := by
          rcases Subgroup.Normal.eq_bot_or_eq_top (K.subgroupOf L) with hb | ht
          · exfalso
            have hdisj : Disjoint K L := Subgroup.subgroupOf_eq_bot.mp hb
            have hbot : K = ⊥ := by
              rw [Subgroup.eq_bot_iff_forall]
              intro x hx
              have h2 : x ∈ K ⊓ L := Subgroup.mem_inf.mpr ⟨hx, hKleL hx⟩
              rw [disjoint_iff.mp hdisj, Subgroup.mem_bot] at h2
              exact h2
            exact hKne hbot
          · exact le_antisymm hKleL (Subgroup.subgroupOf_eq_top.mp ht)
        haveI hKsimple : IsSimpleGroup ↥K :=
          isSimpleGroup_of_mulEquiv (MulEquiv.subgroupCongr hKL).symm
        have hCbot : g.ker = ⊥ := by
          rcases Subgroup.Normal.eq_bot_or_eq_top g.ker with h | h
          · exact h
          · exfalso
            have hone : ∀ x : ↥K, g x = 1 :=
              fun x => MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x)
            have hsub : Subsingleton (↥E ⧸ Subgroup.center ↥E) := ⟨fun y y' => by
              obtain ⟨x, rfl⟩ := hg_surj y
              obtain ⟨x', rfl⟩ := hg_surj y'
              rw [hone x, hone x']⟩
            obtain ⟨a, b, hab⟩ :=
              (inferInstance : Nontrivial (↥E ⧸ Subgroup.center ↥E)).exists_pair_ne
            exact hab (hsub.elim a b)
        have hbij : Function.Bijective g := ⟨(MonoidHom.ker_eq_bot_iff g).mp hCbot, hg_surj⟩
        exact Or.inr ⟨p, k, hp, hoddp, hq,
          ⟨(MulEquiv.ofBijective g hbij).symm.trans ((MulEquiv.subgroupCongr hKL).trans eL)⟩⟩
      · -- `L ≅ PGL(2, q)`: use the `PSL(2,q) ⊆ PGL(2,q)` inside `L`
        obtain ⟨eL⟩ := hPGLis
        obtain ⟨M, hMleL, hMnL, hMsimp, ⟨eM⟩, hLL⟩ :=
          exists_normal_psl_in_overgroup L p k hoddp hq eL
        haveI hMsimp' : IsSimpleGroup ↥M := hMsimp
        -- the projection `↥K →* ↥L ⧸ M` has kernel `M.subgroupOf K`
        let gam : ↥K →* (↥L ⧸ M.subgroupOf L) :=
          (QuotientGroup.mk' (M.subgroupOf L)).comp (Subgroup.inclusion hKleL)
        have hgamker : gam.ker = M.subgroupOf K := by
          ext z
          rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
          show QuotientGroup.mk' (M.subgroupOf L) (Subgroup.inclusion hKleL z) = 1 ↔
            (z : X ⧸ Work.GW2.oddCore X) ∈ M
          rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf, inclusion_coe]
        haveI : IsMulCommutative (↥L ⧸ M.subgroupOf L) :=
          isMulCommutative_quotient_of_commutator_le (M.subgroupOf L) hLL
        haveI : Group.IsSolvable (↥L ⧸ M.subgroupOf L) := inferInstance
        have hM_normal_M : ((M ⊓ K).subgroupOf M).Normal := by
          refine Subgroup.Normal.mk fun n hn m => ?_
          rw [Subgroup.mem_subgroupOf] at hn ⊢
          obtain ⟨hnM, hnK⟩ := Subgroup.mem_inf.mp hn
          refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
          · show (m : X ⧸ Work.GW2.oddCore X) * (n : X ⧸ Work.GW2.oddCore X) *
              (m : X ⧸ Work.GW2.oddCore X)⁻¹ ∈ M
            exact conj_mem_of_subgroupOf_normal hMnL hMleL hnM (hMleL m.2)
          · show (m : X ⧸ Work.GW2.oddCore X) * (n : X ⧸ Work.GW2.oddCore X) *
              (m : X ⧸ Work.GW2.oddCore X)⁻¹ ∈ K
            exact hKnorm.conj_mem (n : X ⧸ Work.GW2.oddCore X) hnK (m : X ⧸ Work.GW2.oddCore X)
        by_cases hMleK : M ≤ K
        · -- `M ≤ K`
          have hMnK : (M.subgroupOf K).Normal := by
            have h1 : (M.subgroupOf L).comap (Subgroup.inclusion hKleL) = M.subgroupOf K := by
              ext x
              rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
                inclusion_coe]
            rw [← h1]
            exact hMnL.comap (Subgroup.inclusion hKleL)
          let gM : ↥M →* (↥E ⧸ Subgroup.center ↥E) := g.comp (Subgroup.inclusion hMleK)
          have hgM_range : gM.range = Subgroup.map g (M.subgroupOf K) := by
            ext y
            rw [MonoidHom.mem_range, Subgroup.mem_map]
            constructor
            · rintro ⟨x, rfl⟩
              exact ⟨⟨(x : X ⧸ Work.GW2.oddCore X), hMleK x.2⟩,
                mem_subgroupOf_of_le hMleK x.2, rfl⟩
            · rintro ⟨z, hz, rfl⟩
              refine ⟨⟨(z : X ⧸ Work.GW2.oddCore X), Subgroup.mem_subgroupOf.mp hz⟩, ?_⟩
              simp [gM, g, Subgroup.inclusion]
          have hgM_normal : gM.range.Normal :=
            hgM_range ▸ Subgroup.Normal.map hMnK g hg_surj
          rcases Subgroup.Normal.eq_bot_or_eq_top gM.range with hbot | htop
          · -- `M ≤ ker g`: `S` is a quotient of `↥K ⧸ M`, a subgroup of the abelian `L ⧸ M`
            exfalso
            have hMker : M.subgroupOf K ≤ g.ker := by
              intro z hz
              rw [MonoidHom.mem_ker]
              have hz' : gM ⟨(z : X ⧸ Work.GW2.oddCore X), Subgroup.mem_subgroupOf.mp hz⟩ =
                  1 := by
                have hmem : gM ⟨(z : X ⧸ Work.GW2.oddCore X), Subgroup.mem_subgroupOf.mp hz⟩ ∈
                    gM.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
                rwa [hbot, Subgroup.mem_bot] at hmem
              simpa [gM, g, Subgroup.inclusion] using hz'
            have hgam_le : gam.ker ≤ g.ker := by rw [hgamker]; exact hMker
            haveI : Group.IsSolvable (↥K ⧸ gam.ker) :=
              Group.isSolvable_of_isSolvable_injective
                (f := (QuotientGroup.quotientKerEquivRange gam).toMonoidHom)
                (QuotientGroup.quotientKerEquivRange gam).injective
            exact hSnsolv (Group.isSolvable_of_surjective
              (f := QuotientGroup.lift gam.ker g hgam_le)
              (QuotientGroup.lift_surjective_of_surjective _ g hg_surj hgam_le))
          · -- `S ≅ ↥M ≅ PSL(2, q)`
            have hgM_surj : Function.Surjective gM := MonoidHom.range_eq_top.mp htop
            have hker_bot : gM.ker = ⊥ := by
              rcases Subgroup.Normal.eq_bot_or_eq_top gM.ker with hb | ht
              · exact hb
              · exfalso
                have hone : ∀ x : ↥M, gM x = 1 :=
                  fun x => MonoidHom.mem_ker.mp (ht ▸ Subgroup.mem_top x)
                have hrange : gM.range = ⊥ := by
                  rw [Subgroup.eq_bot_iff_forall]
                  intro y hy
                  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
                  exact hone x
                rw [hrange] at htop
                exact bot_ne_top htop
            have hbij : Function.Bijective gM :=
              ⟨(MonoidHom.ker_eq_bot_iff gM).mp hker_bot, hgM_surj⟩
            exact Or.inr ⟨p, k, hp, hoddp, hq,
              ⟨(MulEquiv.ofBijective gM hbij).symm.trans eM⟩⟩
        · -- `M ⊄ K`: then `M ⊓ K = ⊥` and `↥K` embeds into the commutative `L ⧸ M`
          exfalso
          have hMK : M ⊓ K = ⊥ := by
            haveI := hM_normal_M
            rcases Subgroup.Normal.eq_bot_or_eq_top ((M ⊓ K).subgroupOf M) with hb | ht
            · have h1 : M ⊓ K ⊓ M = ⊥ := disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hb)
              rwa [inf_eq_left.mpr inf_le_left] at h1
            · exfalso
              exact hMleK ((Subgroup.subgroupOf_eq_top.mp ht).trans inf_le_right)
          have hgamker_bot : gam.ker = ⊥ := by
            rw [hgamker, Subgroup.subgroupOf_eq_bot, disjoint_iff]
            exact hMK
          have hinj : Function.Injective gam := (MonoidHom.ker_eq_bot_iff gam).mp hgamker_bot
          haveI : Group.IsSolvable ↥K :=
            Group.isSolvable_of_isSolvable_injective (f := gam) hinj
          exact hSnsolv (Group.isSolvable_of_surjective (f := g) hg_surj)

end Work.DSTR
