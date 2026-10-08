import Mathlib
import Submission.Work.Hering.AppVII.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Appendix VII of Peterfalvi I (p. 216) in conjugation form

Peterfalvi I, Appendix VII, as formalised in `Submission.Work.Hering.AppVII.Defs`
(`AppVIIProp`), is a statement about a finite group `A` acting **by group automorphisms**
(`MulDistribMulAction`) on a finite group `K`: if `P, Q ≤ A` with `Q` normal, `P ⊓ Q = ⊥`,
`P ⊔ Q = ⊤`, `|P| = p` prime, `p ∤ |Q|`, `(|K|,|A|) = 1` and `|C_Q(P)|` odd, then `K` is generated
by the fixed points of `⁅P,Q⁆` together with the fixed points of the conjugates `P^x`, `x ∈ Q`.

For the reduction step of Hering (Peterfalvi I, Chapter IV, §2, Step 5) this has to be applied to
the *conjugation* action of a subgroup `L = P ⋊ Q` of `G` on a **normal subgroup** `V ⊴ G`:
there is no `MulDistribMulAction ↥L ↥V` in the library, only the conjugation `MulAction` of
`Submission.Work.Hering.Perm.Defs`.

This file supplies that action (`MulAut.conjNormal`, restricted to `L`) and transfers the
conclusion of `AppVIIProp` back to `G`, giving the lemma in the form the reduction needs: for
`V ⊴ G`, `L ≤ G`, `P, Q ≤ L`, `(Q.subgroupOf L).Normal`, `P ⊓ Q = ⊥`, `P ⊔ Q = L`,
`|P| = p` prime, `p ∤ |Q|`, `(|V|,|L|) = 1` and `|C_Q(P)|` odd,

`V ≤ ⟪ C_V(⁅P,Q⁆) ∪ ⋃_{x ∈ Q} C_V(P^x) ⟫`.

The conjugation action of `L = P ⋊ Q` on `V` makes `V` an `L`-module (in the multiplicative
sense), and `⁅P,Q⁆`, `P^x` are computed inside `L`, so Appendix VII applies verbatim; the only
content is the translation of the two fixed-point sets between `↥L`/`↥V` and `G`.
-/

namespace Work.Hering.Step5

/-! ## Elementary transfer lemmas for `Subgroup.subgroupOf` -/

/-- Commutators are preserved by `subgroupOf`: if `P, Q ≤ L` then the commutator of the traces
`P ∩ L`, `Q ∩ L` inside `L` is the trace of the commutator `⁅P, Q⁆`. -/
theorem commutator_subgroupOf_eq {G : Type*} [Group G] {P Q L : Subgroup G} (hPL : P ≤ L)
    (hQL : Q ≤ L) : (⁅P, Q⁆).subgroupOf L = ⁅P.subgroupOf L, Q.subgroupOf L⁆ := by
  have hcomm : ⁅P, Q⁆ ≤ L := (Subgroup.commutator_mono hPL hQL).trans (Subgroup.commutator_le_self L)
  apply Subgroup.map_injective (Subgroup.subtype_injective L)
  simp only [Subgroup.subgroupOf, Subgroup.map_commutator, Subgroup.map_comap_eq,
    Subgroup.range_subtype]
  rw [inf_eq_right.mpr hcomm, inf_eq_right.mpr hPL, inf_eq_right.mpr hQL]

/-- If `P ⊔ Q = L` with `P, Q ≤ L` then the traces of `P` and `Q` generate `L`. -/
theorem sup_subgroupOf_of_sup_eq {G : Type*} [Group G] {P Q L : Subgroup G} (hPL : P ≤ L)
    (hQL : Q ≤ L) (hsup : P ⊔ Q = L) : P.subgroupOf L ⊔ Q.subgroupOf L = ⊤ := by
  apply Subgroup.map_injective (Subgroup.subtype_injective L)
  simp only [Subgroup.subgroupOf, Subgroup.map_sup, Subgroup.map_comap_eq, Subgroup.range_subtype,
    Subgroup.map_top]
  rw [inf_eq_right.mpr hPL, inf_eq_right.mpr hQL, hsup]

/-- The centraliser commutes with `subgroupOf`: for `P ≤ L`, centralising `P` inside `L` is the
same as centralising the trace of `P` inside `L`. -/
theorem centralizer_subgroupOf_of_le {G : Type*} [Group G] {P L : Subgroup G} (hPL : P ≤ L) :
    (Subgroup.centralizer (P : Set G)).subgroupOf L =
      Subgroup.centralizer (P.subgroupOf L : Set ↥L) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    exact Subtype.ext (h (y : G) (Subgroup.mem_subgroupOf.mp hy))
  · intro h y hy
    exact congrArg Subtype.val (h ⟨y, hPL hy⟩ (Subgroup.mem_subgroupOf.mpr hy))

/-- Conjugating inside `L` and then including into `G` is conjugating by the image: for `P ≤ L`
and `x : ↥L`, the image in `G` of the conjugate of `P ∩ L` by `x` is the conjugate of `P` by the
image of `x`. -/
theorem map_conj_subgroupOf_map {G : Type*} [Group G] {P L : Subgroup G} (hPL : P ≤ L)
    (x : ↥L) :
    ((P.subgroupOf L).map (MulAut.conj x).toMonoidHom).map (Subgroup.subtype L) =
      P.map (MulAut.conj ((x : ↥L) : G)).toMonoidHom := by
  ext z
  constructor
  · intro hz
    obtain ⟨z', hz', hz'z⟩ := Subgroup.mem_map.mp hz
    obtain ⟨p, hp, hpz'⟩ := Subgroup.mem_map.mp hz'
    refine Subgroup.mem_map.mpr ⟨(p : G), Subgroup.mem_subgroupOf.mp hp, ?_⟩
    rw [← hz'z, ← congrArg (Subgroup.subtype L) hpz']
    rfl
  · intro hz
    obtain ⟨p, hp, hpz⟩ := Subgroup.mem_map.mp hz
    refine Subgroup.mem_map.mpr ⟨(MulAut.conj x) ⟨p, hPL hp⟩, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨⟨p, hPL hp⟩, Subgroup.mem_subgroupOf.mpr hp, rfl⟩
    · rw [← hpz]
      rfl

/-- Cardinality of the `P`-centralising part of `Q`, computed in `L` or in `G`: the two
subgroups correspond under the inclusion `↥L ↪ G`. -/
theorem card_inf_centralizer_subgroupOf {G : Type*} [Group G] {P Q L : Subgroup G} (hPL : P ≤ L)
    (hQL : Q ≤ L) :
    Nat.card ↥(Q.subgroupOf L ⊓ Subgroup.centralizer (P.subgroupOf L : Set ↥L)) =
      Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G)) := by
  have h1 : Q.subgroupOf L ⊓ Subgroup.centralizer (P.subgroupOf L : Set ↥L) =
      (Q ⊓ Subgroup.centralizer (P : Set G)).subgroupOf L := by
    rw [← centralizer_subgroupOf_of_le hPL]
    change Q.subgroupOf L ⊓ (Subgroup.centralizer (P : Set G)).subgroupOf L
      = Subgroup.comap (Subgroup.subtype L) (Q ⊓ Subgroup.centralizer (P : Set G))
    rw [Subgroup.comap_inf]
    rfl
  rw [h1]
  exact Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (fun x hx => hQL (Subgroup.mem_inf.mp hx).1)).toEquiv

/-! ## Universe invariance of Appendix VII -/

/-- `Subgroup.closure` commutes with the image of a monoid homomorphism. -/
theorem closure_image_map {G H : Type*} [Group G] [Group H] (f : G →* H) (s : Set G) :
    Subgroup.closure (f '' s) = (Subgroup.closure s).map f := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_map_of_mem f (Subgroup.subset_closure hx)
  · rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro x hx
    exact Subgroup.subset_closure ⟨x, hx, rfl⟩

universe u v u' v'

/-- **`AppVIIProp` is independent of the universes of the acting group `A` and of the group `K`.**
Given a proof at universes `(u,v)`, take isomorphic models `A₂`, `K₂` of the goal's groups `A`,
`K` in the universes `u`, `v` (`Finite.exists_type_univ_nonempty_mulEquiv`), transport the action
along the two isomorphisms by `a • k := eK (eA.symm a • eK.symm k)`, and transport the conclusion
back. All ingredients of `AppVIIProp` (`Subgroup.map`, `Nat.card`, `⁅_,_⁆`, `Subgroup.centralizer`,
`Subgroup.closure`, `⊓`, `⊔`, `Subgroup.Normal`) are invariant under such isomorphisms. -/
theorem appVIIProp_univ_aux (h : AppVIIProp.{u, v}) : AppVIIProp.{u', v'} := by
  intro A instA finA P Q hQn hinf hsup p hp hcardP hpQ K instK finK instAct hcop hodd
  letI : Group A := instA
  letI : Finite A := finA
  letI : Group K := instK
  letI : Finite K := finK
  letI : MulDistribMulAction A K := instAct
  -- isomorphic models of `A` and `K` in the universes of the hypothesis
  obtain ⟨A₂, instA₂, finA₂, ⟨eA⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{u', u} A
  letI : Group A₂ := instA₂
  letI : Fintype A₂ := finA₂
  obtain ⟨K₂, instK₂, finK₂, ⟨eK⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{v', v} K
  letI : Group K₂ := instK₂
  letI : Fintype K₂ := finK₂
  -- the transported action of `A₂` on `K₂`
  let act₂ : MulDistribMulAction A₂ K₂ :=
    { smul := fun a k => eK (eA.symm a • eK.symm k)
      one_smul := fun k => by
        show eK (eA.symm 1 • eK.symm k) = k
        rw [map_one, one_smul, eK.apply_symm_apply]
      mul_smul := fun a b k => by
        show eK (eA.symm (a * b) • eK.symm k)
          = eK (eA.symm a • eK.symm (eK (eA.symm b • eK.symm k)))
        rw [map_mul, mul_smul, eK.symm_apply_apply]
      smul_one := fun a => by
        show eK (eA.symm a • eK.symm 1) = 1
        rw [map_one, smul_one, map_one]
      smul_mul := fun a m n => by
        show eK (eA.symm a • eK.symm (m * n))
          = eK (eA.symm a • eK.symm m) * eK (eA.symm a • eK.symm n)
        rw [map_mul, smul_mul', map_mul] }
  letI := act₂
  -- the hypotheses of Appendix VII in the transported configuration
  have hQn₂ : (Q.map eA.toMonoidHom).Normal := hQn.map eA.toMonoidHom eA.surjective
  have hinf₂ : P.map eA.toMonoidHom ⊓ Q.map eA.toMonoidHom = ⊥ := by
    rw [← Subgroup.map_inf P Q eA.toMonoidHom eA.injective, hinf, Subgroup.map_bot]
  have hsup₂ : P.map eA.toMonoidHom ⊔ Q.map eA.toMonoidHom = ⊤ := by
    rw [← Subgroup.map_sup P Q eA.toMonoidHom, hsup,
      Subgroup.map_top_of_surjective eA.toMonoidHom eA.surjective]
  have hcardP₂ : Nat.card ↥(P.map eA.toMonoidHom) = p := by
    rw [Subgroup.card_map_of_injective (K := P) eA.injective]
    exact hcardP
  have hpQ₂ : ¬ p ∣ Nat.card ↥(Q.map eA.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (K := Q) eA.injective]
    exact hpQ
  have hcop₂ : Nat.Coprime (Nat.card K₂) (Nat.card A₂) := by
    rw [← Nat.card_congr eK.toEquiv, ← Nat.card_congr eA.toEquiv]
    exact hcop
  have hcent : Subgroup.centralizer ((P.map eA.toMonoidHom : Subgroup A₂) : Set A₂) =
      (Subgroup.centralizer (P : Set A)).map eA.toMonoidHom := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff] at hx
      refine Subgroup.mem_map.mpr ⟨eA.symm x, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h2 := hx (eA y) (Subgroup.mem_map_of_mem eA.toMonoidHom hy)
      have h3 := congrArg (fun t => eA.symm t) h2
      simpa using h3
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      rintro z ⟨w, hw, rfl⟩
      show eA w * eA y = eA y * eA w
      rw [← map_mul, ← map_mul, hy w hw]
  have hodd₂ : Odd (Nat.card ↥(Q.map eA.toMonoidHom
      ⊓ Subgroup.centralizer ((P.map eA.toMonoidHom : Subgroup A₂) : Set A₂))) := by
    have h1 : Q.map eA.toMonoidHom
        ⊓ Subgroup.centralizer ((P.map eA.toMonoidHom : Subgroup A₂) : Set A₂) =
        (Q ⊓ Subgroup.centralizer (P : Set A)).map eA.toMonoidHom := by
      rw [hcent, Subgroup.map_inf Q _ eA.toMonoidHom eA.injective]
    rw [h1, Subgroup.card_map_of_injective (K := Q ⊓ Subgroup.centralizer (P : Set A))
      eA.injective]
    exact hodd
  -- Appendix VII in the transported configuration
  have happ := h (P.map eA.toMonoidHom) (Q.map eA.toMonoidHom) hQn₂ hinf₂ hsup₂ p hp hcardP₂ hpQ₂
    hcop₂ hodd₂
  -- the two fixed-point sets of the Appendix, in `K` and in `K₂`
  let U₁ : Set K := {k | ∀ y ∈ (⁅P, Q⁆ : Subgroup A), y • k = k}
  let U₂ : Set K := {k | ∃ x : ↥Q, ∀ y ∈ P.map (MulAut.conj (x : A)).toMonoidHom, y • k = k}
  let U₁' : Set K₂ :=
    {k | ∀ y ∈ (⁅P.map eA.toMonoidHom, Q.map eA.toMonoidHom⁆ : Subgroup A₂), y • k = k}
  let U₂' : Set K₂ :=
    {k | ∃ x : ↥(Q.map eA.toMonoidHom),
      ∀ y ∈ (P.map eA.toMonoidHom).map (MulAut.conj (x : A₂)).toMonoidHom, y • k = k}
  have happ' : Subgroup.closure (U₁' ∪ U₂') = ⊤ := happ
  -- `eA a` fixes `k : K₂` exactly when `a` fixes `eK.symm k`
  have smul_iff : ∀ (a : A) (k : K₂),
      eA.toMonoidHom a • k = k ↔ a • (eK.symm k) = eK.symm k := by
    intro a k
    have key : eA.toMonoidHom a • k = eK (a • eK.symm k) :=
      congrArg (fun t => eK (t • eK.symm k)) (eA.symm_apply_apply a)
    constructor
    · intro h
      have h1 : eK (a • eK.symm k) = k := key ▸ h
      exact (eK.symm_apply_apply (a • eK.symm k)).symm.trans (congrArg eK.symm h1)
    · intro h
      rw [key, h, eK.apply_symm_apply]
  -- the isomorphism `eA` commutes with conjugation
  have conj_eq : ∀ a p : A,
      eA.toMonoidHom (MulAut.conj a p) = MulAut.conj (eA.toMonoidHom a) (eA.toMonoidHom p) := by
    intro a p
    show eA (a * p * a⁻¹) = eA a * eA p * (eA a)⁻¹
    rw [map_mul, map_mul, map_inv]
  have hU₁ : ∀ k : K₂, (k ∈ U₁' ↔ eK.symm k ∈ U₁) := by
    intro k
    constructor
    · intro hk a ha
      have hmem : eA.toMonoidHom a ∈
          (⁅P.map eA.toMonoidHom, Q.map eA.toMonoidHom⁆ : Subgroup A₂) := by
        rw [← Subgroup.map_commutator P Q eA.toMonoidHom]
        exact Subgroup.mem_map_of_mem eA.toMonoidHom ha
      exact (smul_iff a k).mp (hk (eA.toMonoidHom a) hmem)
    · intro hk y hy
      rw [← Subgroup.map_commutator P Q eA.toMonoidHom] at hy
      obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp hy
      have h2 := (smul_iff a k).mpr (hk a ha)
      rw [hay] at h2
      exact h2
  have hU₂ : ∀ k : K₂, (k ∈ U₂' ↔ eK.symm k ∈ U₂) := by
    intro k
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨a, haQ, hax⟩ := Subgroup.mem_map.mp x.2
      refine ⟨⟨a, haQ⟩, ?_⟩
      intro y hy
      obtain ⟨p, hp, hpy⟩ := Subgroup.mem_map.mp hy
      have hmem : eA.toMonoidHom (MulAut.conj a p) ∈
          (P.map eA.toMonoidHom).map (MulAut.conj (x : A₂)).toMonoidHom := by
        rw [Subgroup.mem_map]
        refine ⟨eA.toMonoidHom p, Subgroup.mem_map_of_mem eA.toMonoidHom hp, ?_⟩
        rw [← hax]
        exact (conj_eq a p).symm
      have h4 := hx (eA.toMonoidHom (MulAut.conj a p)) hmem
      have h5 := (smul_iff (MulAut.conj a p) k).mp h4
      rw [← hpy]
      exact h5
    · rintro ⟨⟨a, haQ⟩, ha⟩
      refine ⟨⟨eA.toMonoidHom a, Subgroup.mem_map_of_mem eA.toMonoidHom haQ⟩, ?_⟩
      intro y hy
      obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hy
      obtain ⟨p, hp, hpw⟩ := Subgroup.mem_map.mp hw
      have h3 := (smul_iff (MulAut.conj a p) k).mpr
        (ha (MulAut.conj a p) (Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hp))
      have hy_eq : eA.toMonoidHom (MulAut.conj a p) = y := by
        rw [← hwy, ← hpw]
        exact conj_eq a p
      rw [hy_eq] at h3
      exact h3
  -- the two fixed-point sets of `K` and of `K₂` correspond under `eK`
  have hU : eK.toMonoidHom '' (U₁ ∪ U₂) = U₁' ∪ U₂' := by
    ext k
    constructor
    · rintro ⟨k', hk', rfl⟩
      rcases hk' with hk' | hk'
      · exact Or.inl ((hU₁ (eK.toMonoidHom k')).mpr (by simpa using hk'))
      · exact Or.inr ((hU₂ (eK.toMonoidHom k')).mpr (by simpa using hk'))
    · intro hk
      rcases hk with hk | hk
      · exact ⟨eK.symm k, Or.inl ((hU₁ k).mp hk), by simp⟩
      · exact ⟨eK.symm k, Or.inr ((hU₂ k).mp hk), by simp⟩
  have hmain : Subgroup.closure (U₁ ∪ U₂) = ⊤ := by
    apply Subgroup.map_injective (f := eK.toMonoidHom) eK.injective
    rw [Subgroup.map_top_of_surjective eK.toMonoidHom eK.surjective,
      ← closure_image_map eK.toMonoidHom (U₁ ∪ U₂), hU, happ']
  exact hmain

/-- **Appendix VII of Peterfalvi I (p. 216), conjugation form.** Let `V ⊴ G` and let
`L = P ⋊ Q ≤ G` with `P ⊓ Q = ⊥`, `|P| = p` prime, `p ∤ |Q|`, `(|V|, |L|) = 1` and `|C_Q(P)|`
odd. Then `V` is generated by the elements of `V` centralising `⁅P,Q⁆` together with those
centralising a conjugate `P^x` of `P` by an element `x ∈ Q`.

The point is that `L` acts on `V` by conjugation (a *group* automorphism action, i.e.
`MulDistribMulAction ↥L ↥V`, which the Appendix requires), and `L` is the semidirect product
`P ⋊ Q`; the statement is then exactly `AppVIIProp` transported along `↥L ↪ G` and `↥V ↪ G`. -/
theorem appVII_conj {G : Type*} [Group G] [Finite G] (hAppVII : AppVIIProp)
    {V : Subgroup G} (hV : V.Normal) {L P Q : Subgroup G} (hPL : P ≤ L) (hQL : Q ≤ L)
    (hQn : (Q.subgroupOf L).Normal)
    (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = L)
    {p : ℕ} (hp : p.Prime) (hcardP : Nat.card P = p) (hpQ : ¬ p ∣ Nat.card Q)
    (hcop : Nat.Coprime (Nat.card V) (Nat.card L))
    (hodd : Odd (Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G)))) :
    V ≤ Subgroup.closure ({v : G | v ∈ V ∧ ∀ y ∈ ⁅P, Q⁆, y * v * y⁻¹ = v} ∪
      {v : G | v ∈ V ∧ ∃ x : ↥Q,
        ∀ y ∈ P.map (MulAut.conj ((x : ↥Q) : G)).toMonoidHom, y * v * y⁻¹ = v}) := by
  classical
  haveI hVn : V.Normal := hV
  -- the conjugation action of `L` on the normal subgroup `V`, as an action by group automorphisms
  let act : MulDistribMulAction ↥L ↥V :=
    { smul := fun l v => MulAut.conjNormal (l : G) v
      one_smul := fun v => by
        show MulAut.conjNormal (((1 : ↥L) : G)) v = v
        simp
      mul_smul := fun a b v => by
        show MulAut.conjNormal ((a * b : ↥L) : G) v
          = MulAut.conjNormal (a : G) (MulAut.conjNormal (b : G) v)
        rw [show ((a * b : ↥L) : G) = (a : G) * (b : G) from rfl, map_mul]
        rfl
      smul_one := fun l => by
        show MulAut.conjNormal (l : G) 1 = 1
        simp
      smul_mul := fun l m n => by
        show MulAut.conjNormal (l : G) (m * n)
          = MulAut.conjNormal (l : G) m * MulAut.conjNormal (l : G) n
        simp }
  letI := act
  -- the hypotheses of Appendix VII, transported from `G` to `L`
  have hinf' : P.subgroupOf L ⊓ Q.subgroupOf L = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hx1 : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).1
    have hx2 : (x : G) ∈ Q := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).2
    have h3 : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hinf]
      exact Subgroup.mem_inf.mpr ⟨hx1, hx2⟩
    exact Subgroup.mem_bot.mpr (Subtype.ext (by simpa using h3))
  have hsup' : P.subgroupOf L ⊔ Q.subgroupOf L = ⊤ :=
    sup_subgroupOf_of_sup_eq hPL hQL hsup
  have hcardP' : Nat.card ↥(P.subgroupOf L) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv]
    exact hcardP
  have hpQ' : ¬ p ∣ Nat.card ↥(Q.subgroupOf L) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv]
    exact hpQ
  have hodd' : Odd (Nat.card ↥(Q.subgroupOf L ⊓
      Subgroup.centralizer ((P.subgroupOf L : Subgroup ↥L) : Set ↥L))) := by
    rw [card_inf_centralizer_subgroupOf hPL hQL]
    exact hodd
  -- Appendix VII with `A = ↥L`, `K = ↥V`
  have happ := appVIIProp_univ_aux hAppVII (P.subgroupOf L) (Q.subgroupOf L) hQn hinf' hsup' p hp
    hcardP' hpQ' (K := ↥V) hcop hodd'
  -- each of the two generating sets of the Appendix lies in the corresponding set for `G`
  have key : (⊤ : Subgroup ↥V) ≤ Subgroup.comap (Subgroup.subtype V)
      (Subgroup.closure ({v : G | v ∈ V ∧ ∀ y ∈ ⁅P, Q⁆, y * v * y⁻¹ = v} ∪
        {v : G | v ∈ V ∧ ∃ x : ↥Q,
          ∀ y ∈ P.map (MulAut.conj ((x : ↥Q) : G)).toMonoidHom, y * v * y⁻¹ = v})) := by
    have h' : Subgroup.closure
        ({k : ↥V | ∀ y ∈ (⁅P.subgroupOf L, Q.subgroupOf L⁆ : Subgroup ↥L), y • k = k} ∪
          {k : ↥V | ∃ x : ↥(Q.subgroupOf L),
            ∀ y ∈ (P.subgroupOf L).map (MulAut.conj (x : ↥L)).toMonoidHom, y • k = k}) = ⊤ :=
      happ
    rw [← h']
    rw [Subgroup.closure_le]
    rintro k (h1 | h2)
    · -- `k` is fixed by `⁅P, Q⁆`
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      refine Subgroup.subset_closure (Or.inl ?_)
      refine ⟨k.2, ?_⟩
      intro y hy
      have hyL : y ∈ L :=
        (Subgroup.commutator_mono hPL hQL).trans (Subgroup.commutator_le_self L) hy
      have hy' : (⟨y, hyL⟩ : ↥L) ∈ ⁅P.subgroupOf L, Q.subgroupOf L⁆ := by
        rw [← commutator_subgroupOf_eq hPL hQL]
        exact Subgroup.mem_subgroupOf.mpr hy
      have hfix := h1 ⟨y, hyL⟩ hy'
      have hval := congrArg (fun t : ↥V => (t : G)) hfix
      rw [show (((⟨y, hyL⟩ : ↥L) • k : ↥V) : G)
        = MulAut.conjNormal ((⟨y, hyL⟩ : ↥L) : G) k from rfl, MulAut.conjNormal_apply] at hval
      simpa using hval
    · -- `k` is fixed by a conjugate `P ^ x`, `x ∈ Q`
      obtain ⟨x, hx⟩ := h2
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      refine Subgroup.subset_closure (Or.inr ?_)
      refine ⟨k.2, ⟨⟨(x : ↥L), Subgroup.mem_subgroupOf.mp x.2⟩, ?_⟩⟩
      intro y hy
      have hy2 : y ∈ ((P.subgroupOf L).map (MulAut.conj (x : ↥L)).toMonoidHom).map
          (Subgroup.subtype L) := by
        rw [map_conj_subgroupOf_map hPL]
        exact hy
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy2
      have hfix := hx z hz
      have hval := congrArg (fun t : ↥V => (t : G)) hfix
      rw [show (((z : ↥L) • k : ↥V) : G)
        = MulAut.conjNormal ((z : ↥L) : G) k from rfl, MulAut.conjNormal_apply] at hval
      rw [← hzy]
      simpa using hval
  intro v hv
  exact key (Subgroup.mem_top (⟨v, hv⟩ : ↥V))

end Work.Hering.Step5
