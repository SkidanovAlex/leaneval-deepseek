import Mathlib
import Submission.Work.ThmF.ChV12.Lemma5Defs
import Submission.Work.ThmF.ChV12.X5isoPSL2_of
import Submission.Work.ThmF.ChV12.psl2_centralizer_torus

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.L_factsAux` — the centraliser of `st` in `X = ⟨Q₀,K,t⟩`

This is the content of `Work.ThmF.ChV12.lemma5d` (Ch. V §2 Lemma 5, the form read by §3
step (15)), re-derived here on a **clash-free import cone**: the module
`Submission.Work.ThmF.ChV12.lemma5d` transitively imports `Submission.Work.ThreePoints.Main`,
which imports `Submission.Work.ThreePoints.p3cd_torus_cyclic`; that file and
`Submission.Work.ThreePoints.sec4_prop2b` both declare the constant
`Work.ThreePoints.s4prop2_brsz`, so any environment containing the Ch. V §3 chain
(`… → Submission.Work.ThmF.ChV3.Chain17 → … → Submission.Work.ThmF.ChV12.lemma2c_sylow →
Submission.Work.ThreePoints.sec4_prop2b`) *and* `lemma5d` is inconsistent.

The mathematics is unchanged: `X5isoPSL2_of` (Ch. V §2 Lemma 5 (c)) identifies
`↥(X5 H t)` with `PSL(2,2ⁿ)` and `psl2_centralizer_torus` is the model fact about the
centraliser of an order-`3` element of `PSL(2,2ⁿ)`; the proof below is exactly the transport
argument of `lemma5d_of_iso`.

Nothing here is a novelty — it is the same theorem on the import cone that the Ch. V §3
statement needs.  The three transport lemmas are restated with fresh names so that they cannot
collide with `Work.ThmF.ChV12`'s copies.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.ChV3.Prove

/-! ## Transport lemmas -/

/-- Cyclicity is preserved by a group isomorphism. -/
theorem lf_isCyclic_of_mulEquiv {M N : Type*} [Group M] [Group N] (e : M ≃* N) (h : IsCyclic M) :
    IsCyclic N := by
  rw [isCyclic_iff_exists_zpowers_eq_top] at h ⊢
  obtain ⟨g, hg⟩ := h
  refine ⟨e g, ?_⟩
  have hmap : Subgroup.map e.toMonoidHom (Subgroup.zpowers g) = Subgroup.zpowers (e g) :=
    MonoidHom.map_zpowers e.toMonoidHom g
  rw [← hmap, hg, Subgroup.map_top_of_surjective _ e.surjective]

/-- The centraliser of an element `x` of a subgroup `S ≤ G`, viewed inside `S`, maps onto
`S ⊓ C_G(x)`. -/
theorem lf_map_centralizer_subtype {G : Type*} [Group G] (S : Subgroup G) (x : G) (hx : x ∈ S) :
    (Subgroup.centralizer ({⟨x, hx⟩} : Set ↥S)).map S.subtype =
      S ⊓ Subgroup.centralizer ({x} : Set G) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hz))
  · rintro ⟨hyS, hy⟩
    refine ⟨⟨y, hyS⟩, ?_, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hy))

/-- The centraliser of an element, transported along a group isomorphism. -/
theorem lf_map_centralizer_mulEquiv {M N : Type*} [Group M] [Group N] (e : M ≃* N) (g : M) :
    (Subgroup.centralizer ({g} : Set M)).map e.toMonoidHom =
      Subgroup.centralizer ({e g} : Set N) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h := Subgroup.mem_centralizer_singleton_iff.mp hx
    show e.toMonoidHom x * e.toMonoidHom g = e.toMonoidHom g * e.toMonoidHom x
    rw [← map_mul, ← map_mul, h]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h := Subgroup.mem_centralizer_singleton_iff.mp hy
    refine e.injective ?_
    calc e (e.symm y * g) = e (e.symm y) * e g := map_mul _ _ _
      _ = y * e g := by rw [e.apply_symm_apply]
      _ = e g * y := h
      _ = e g * e (e.symm y) := by rw [e.apply_symm_apply]
      _ = e (g * e.symm y) := (map_mul _ _ _).symm

/-! ## The transport step -/

variable {G : Type} [Group G] [Finite G]

/-- **The transport step**: given split rank-one data with `st` of order `3`, the identification
`Φ : ↥(X5 H t) ≃* PSL(2,2ⁿ)` (with `|Q₀| = 2ⁿ`, `n ≥ 2`) and the model fact
`psl2_centralizer_torus`, the centraliser of `st` in `X5 H t` is cyclic of order `|Q₀| + 1` and
is inverted by `s`. -/
theorem lemma5d_iso_free {H Q : Subgroup G} {t s : G}
    (h : Work.ThmF.Lemma5.Hyp5 H Q t s) (hq : 3 ∣ Nat.card ↥(Work.ThmF.Q0sub H) + 1)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ n)
    (Φ : ↥(Work.ThmF.Lemma5.X5 H t) ≃* PSL2Model n) :
    IsCyclic ↥(Work.ThmF.Lemma5.X5 H t ⊓ Subgroup.centralizer ({s * t} : Set G)) ∧
      Nat.card ↥(Work.ThmF.Lemma5.X5 H t ⊓ Subgroup.centralizer ({s * t} : Set G)) =
        Nat.card ↥(Work.ThmF.Q0sub H) + 1 ∧
      ∀ x ∈ Work.ThmF.Lemma5.X5 H t ⊓ Subgroup.centralizer ({s * t} : Set G),
        s * x * s⁻¹ = x⁻¹ := by
  classical
  -- `s` lies in `X5 H t`
  have hsQ0 : s ∈ Work.ThmF.Q0 H := Or.inl ⟨h.split.le h.s_mem, h.s_inv⟩
  have hsX : s ∈ Work.ThmF.Lemma5.X5 H t := Work.ThmF.Lemma5.Q0_subset_X5 H t hsQ0
  -- the elements `s`, `t` of `X5 H t`
  set sX : ↥(Work.ThmF.Lemma5.X5 H t) := ⟨s, hsX⟩ with hsXdef
  set tX : ↥(Work.ThmF.Lemma5.X5 H t) := Work.ThmF.Lemma5.tX H t with htXdef
  have hsord : orderOf sX = 2 := by
    rw [hsXdef, Subgroup.orderOf_mk]; exact h.s_inv
  have htord : orderOf tX = 2 := by
    rw [htXdef, Work.ThmF.Lemma5.tX, Subgroup.orderOf_mk]; exact h.split.invol
  have hstord : orderOf (sX * tX) = 3 := by
    have hcoe : (((sX * tX : ↥(Work.ThmF.Lemma5.X5 H t)) : G)) = s * t := by
      rw [Subgroup.coe_mul, hsXdef, htXdef, Work.ThmF.Lemma5.tX]
    rw [← Subgroup.orderOf_coe (sX * tX), hcoe]
    exact h.ord3
  -- the two involutions in the model
  have haord : orderOf (Φ sX) = 2 := by rw [MulEquiv.orderOf_eq, hsord]
  have hbord : orderOf (Φ tX) = 2 := by rw [MulEquiv.orderOf_eq, htord]
  have habord : orderOf (Φ sX * Φ tX) = 3 := by
    rw [← map_mul, MulEquiv.orderOf_eq, hstord]
  have h3 : 3 ∣ 2 ^ n + 1 := by rw [← hcard]; exact hq
  obtain ⟨hcyc, hcardC, hinv⟩ :=
    Work.ThmF.ChV12.psl2_centralizer_torus n hn (Φ sX) (Φ tX) haord hbord habord h3
  -- the three subgroups
  let T : Subgroup ↥(Work.ThmF.Lemma5.X5 H t) :=
    Subgroup.centralizer ({sX * tX} : Set ↥(Work.ThmF.Lemma5.X5 H t))
  let Cy : Subgroup (PSL2Model n) := Subgroup.centralizer ({Φ sX * Φ tX} : Set (PSL2Model n))
  have hstX : s * t ∈ Work.ThmF.Lemma5.X5 H t :=
    (Work.ThmF.Lemma5.X5 H t).mul_mem hsX (Work.ThmF.Lemma5.t_mem_X5 H t)
  have hEqst : (⟨s * t, hstX⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) = sX * tX := by
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, hsXdef, htXdef, Work.ThmF.Lemma5.tX]
  have hTmapS : T.map (Work.ThmF.Lemma5.X5 H t).subtype =
      Work.ThmF.Lemma5.X5 H t ⊓ Subgroup.centralizer ({s * t} : Set G) := by
    have h : Subgroup.centralizer ({⟨s * t, hstX⟩} : Set ↥(Work.ThmF.Lemma5.X5 H t)) = T := by
      rw [hEqst]
    rw [← h]
    exact lf_map_centralizer_subtype (Work.ThmF.Lemma5.X5 H t) (s * t) hstX
  have hTmapΦ : T.map Φ.toMonoidHom = Cy := by
    rw [lf_map_centralizer_mulEquiv Φ (sX * tX), map_mul]
  have e1 : ↥T ≃* ↥(Work.ThmF.Lemma5.X5 H t ⊓ Subgroup.centralizer ({s * t} : Set G)) :=
    (Subgroup.equivMapOfInjective T _ (Work.ThmF.Lemma5.X5 H t).subtype_injective).trans
      (MulEquiv.subgroupCongr hTmapS)
  have e2 : ↥T ≃* ↥Cy :=
    (Subgroup.equivMapOfInjective T _ Φ.injective).trans (MulEquiv.subgroupCongr hTmapΦ)
  have hcycT : IsCyclic ↥T := lf_isCyclic_of_mulEquiv e2.symm hcyc
  refine ⟨lf_isCyclic_of_mulEquiv e1 hcycT, ?_, ?_⟩
  · calc Nat.card ↥(Work.ThmF.Lemma5.X5 H t ⊓ Subgroup.centralizer ({s * t} : Set G))
        = Nat.card ↥T := (Nat.card_congr e1.toEquiv).symm
      _ = Nat.card ↥Cy := Nat.card_congr e2.toEquiv
      _ = 2 ^ n + 1 := hcardC
      _ = Nat.card ↥(Work.ThmF.Q0sub H) + 1 := by rw [hcard]
  · intro x hx
    have hxS : x ∈ Work.ThmF.Lemma5.X5 H t := (Subgroup.mem_inf.mp hx).1
    have hxG : x * (s * t) = (s * t) * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
    -- `⟨x, hxS⟩` lies in `T`
    have hxT : (⟨x, hxS⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) ∈ T := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      refine Subtype.ext ?_
      simpa only [Subgroup.coe_mul, hsXdef, htXdef, Work.ThmF.Lemma5.tX] using hxG
    -- its image under `Φ` lies in `Cy`
    have hyCy : Φ ⟨x, hxS⟩ ∈ Cy := by
      rw [← hTmapΦ]
      exact ⟨⟨x, hxS⟩, hxT, rfl⟩
    have h1 := hinv (Φ ⟨x, hxS⟩) hyCy
    have h2 : Φ (sX * ⟨x, hxS⟩ * sX⁻¹) = Φ (⟨x, hxS⟩⁻¹) := by
      rw [map_mul, map_mul, map_inv, map_inv]
      exact h1
    have h3 := congrArg (Subtype.val) (Φ.injective h2)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hsXdef] using h3

/-- **The centraliser of `st` in `X = ⟨Q₀,K,t⟩`**, from the two area inputs `FeitThompsonProp`
and `ChIIFourProp`: `X5 H t ⊓ C_G(st)` is cyclic of order `|Q₀| + 1` and is inverted by `s`.
This is `Work.ThmF.ChV12.lemma5d`, restated on the clash-free import cone. -/
theorem centralizer_st_cyclic {H Q : Subgroup G} {t s : G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (h : Work.ThmF.Lemma5.Hyp5 H Q t s) (hq : 3 ∣ Nat.card ↥(Work.ThmF.Q0sub H) + 1) :
    IsCyclic ↥(Work.ThmF.Lemma5.X5 H t ⊓ Subgroup.centralizer ({s * t} : Set G)) ∧
      Nat.card ↥(Work.ThmF.Lemma5.X5 H t ⊓ Subgroup.centralizer ({s * t} : Set G)) =
        Nat.card ↥(Work.ThmF.Q0sub H) + 1 ∧
      ∀ x ∈ Work.ThmF.Lemma5.X5 H t ⊓ Subgroup.centralizer ({s * t} : Set G),
        s * x * s⁻¹ = x⁻¹ := by
  obtain ⟨n, hn, hcard, ⟨Φ⟩⟩ := Work.ThmF.ChV12.X5isoPSL2_of hFT hC4 h
  exact lemma5d_iso_free h hq hn hcard Φ

end Work.ThmF.ChV3.Prove
