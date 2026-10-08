import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2SixEmbed
import Submission.Work.CORE4.SixConj
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2Seven
import Submission.Work.CORE4.M_eq_layerIn_sup_of_oneInvClass
import Submission.Work.CORE4.DihOrCycSub
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.Case2Setup9S2

namespace Work.CORE4

open Work.GW2 Subgroup

variable {G : Type} [Group G]

/-! ## The conjugation calculus for `conjSub`

`conjSub g A = A.map (MulAut.conj g)` is used throughout §4.  The lemmas below record that it is
a lattice automorphism with the expected composition law, that it commutes with centralizers, and
that it carries normalizers and quasisimplicity along.  The composition law is
`conjSub h (conjSub g A) = conjSub (h * g) A`: as functions, `(conj h) ∘ (conj g) = conj (h * g)`
(note the order). -/

/-- `MulAut.conj g`, as a monoid homomorphism, is multiplication by `g` on both sides. -/
theorem conj_toMonoidHom_apply (g x : G) :
    MulEquiv.toMonoidHom (MulAut.conj g) x = g * x * g⁻¹ := MulAut.conj_apply g x

/-- The same, in the coercion notation used by `Subgroup.map` displays. -/
theorem conj_mulHom_apply (g x : G) : (MulAut.conj g : G →* G) x = g * x * g⁻¹ :=
  MulAut.conj_apply g x

/-- Bridging the two displays of the same monoid homomorphism. -/
theorem map_toMonoidHom_coe (e : G ≃* G) (A : Subgroup G) :
    A.map e.toMonoidHom = A.map (e : G →* G) := rfl

theorem map_conj_conj (h g : G) (A : Subgroup G) :
    (A.map (MulAut.conj g : G →* G)).map (MulAut.conj h : G →* G) =
      A.map (MulAut.conj (h * g) : G →* G) := by
  have hcomp : ((MulAut.conj h : G →* G)).comp (MulAut.conj g : G →* G) =
      (MulAut.conj (h * g) : G →* G) := by
    ext x
    rw [MonoidHom.comp_apply, conj_mulHom_apply, conj_mulHom_apply, conj_mulHom_apply]
    group
  rw [Subgroup.map_map, hcomp]

theorem map_conj_one (A : Subgroup G) :
    A.map (MulAut.conj (1 : G) : G →* G) = A := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rw [conj_mulHom_apply, one_mul, inv_one, mul_one] at hxy
    rwa [← hxy]
  · intro hx
    exact ⟨x, hx, by rw [conj_mulHom_apply, one_mul, inv_one, mul_one]⟩

theorem map_conj_inv (g : G) (A : Subgroup G) :
    (A.map (MulAut.conj g : G →* G)).map (MulAut.conj g⁻¹ : G →* G) = A := by
  rw [map_conj_conj, inv_mul_cancel, map_conj_one]

/-- `conjSub` of the identity is the identity.  (Named `…_six9` to avoid a clash with
`Work.CORE4.conjSub_one` in `Submission/Work/CORE4/Case2LowerBound9.lean`: the two files are
never imported together today, but the duplicate name is a latent hazard.) -/
theorem conjSub_one_six9 (A : Subgroup G) : conjSub (1 : G) A = A := by
  simp only [conjSub]; exact map_conj_one A

/-- `conjSub h ∘ conjSub g = conjSub (h * g)`.  (Named `…_six9` to avoid the clash with
`Work.CORE4.conjSub_conjSub` of `Submission/Work/CORE4/Case2PerXBound9Corrected.lean`: both files
are now imported together by `CORE4/Final3.lean`.) -/
theorem conjSub_conjSub_six9 (h g : G) (A : Subgroup G) :
    conjSub h (conjSub g A) = conjSub (h * g) A := by
  simp only [conjSub]; exact map_conj_conj h g A

/-- `conjSub g⁻¹` is a left inverse of `conjSub g`. -/
theorem conjSub_inv_conjSub (g : G) (A : Subgroup G) :
    conjSub g⁻¹ (conjSub g A) = A := by
  simp only [conjSub]; exact map_conj_inv g A

/-- Conjugation carries the centralizer of a subgroup to the centralizer of its conjugate. -/
theorem conjSub_centralizer (g : G) (E : Subgroup G) :
    conjSub g (Subgroup.centralizer (E : Set G)) =
      Subgroup.centralizer ((conjSub g E : Subgroup G) : Set G) := by
  simp only [conjSub]
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, hcx⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    obtain ⟨e, he, hey⟩ := Subgroup.mem_map.mp hy
    have h : e * c = c * e := Subgroup.mem_centralizer_iff.mp hc e he
    rw [← hcx, ← hey]
    change (MulEquiv.toMonoidHom (MulAut.conj g)) e *
        (MulEquiv.toMonoidHom (MulAut.conj g)) c =
      (MulEquiv.toMonoidHom (MulAut.conj g)) c *
        (MulEquiv.toMonoidHom (MulAut.conj g)) e
    rw [← map_mul, ← map_mul, h]
  · intro hx
    refine Subgroup.mem_map.mpr
      ⟨(MulEquiv.toMonoidHom (MulAut.conj g⁻¹)) x, ?_, ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      intro e he
      have h2 : (MulEquiv.toMonoidHom (MulAut.conj g)) e * x =
          x * (MulEquiv.toMonoidHom (MulAut.conj g)) e :=
        Subgroup.mem_centralizer_iff.mp hx _ (Subgroup.mem_map_of_mem _ he)
      change e * (MulEquiv.toMonoidHom (MulAut.conj g⁻¹)) x =
        (MulEquiv.toMonoidHom (MulAut.conj g⁻¹)) x * e
      apply (MulAut.conj g).injective
      change (MulEquiv.toMonoidHom (MulAut.conj g))
            (e * (MulEquiv.toMonoidHom (MulAut.conj g⁻¹)) x) =
          (MulEquiv.toMonoidHom (MulAut.conj g))
            ((MulEquiv.toMonoidHom (MulAut.conj g⁻¹)) x * e)
      rw [map_mul, map_mul]
      rw [show (MulEquiv.toMonoidHom (MulAut.conj g))
            ((MulEquiv.toMonoidHom (MulAut.conj g⁻¹)) x) = x by
          rw [conj_toMonoidHom_apply, conj_toMonoidHom_apply]; group]
      rw [conj_toMonoidHom_apply] at h2
      exact h2
    · change (MulEquiv.toMonoidHom (MulAut.conj g))
          ((MulEquiv.toMonoidHom (MulAut.conj g⁻¹)) x) = x
      rw [conj_toMonoidHom_apply, conj_toMonoidHom_apply]
      group

/-- The normalizer of a conjugate is the conjugate of the normalizer. -/
theorem normalizer_conjSub (g : G) (E : Subgroup G) :
    Subgroup.normalizer ((conjSub g E : Subgroup G) : Set G) =
      conjSub g (Subgroup.normalizer (E : Set G)) := by
  simp only [conjSub]
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hy
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * y * g, ?_, ?_⟩
    · have h3 : conjSub (g⁻¹ * y * g) E = E := by
        have h4 : conjSub g (conjSub (g⁻¹ * y * g) E) = conjSub g E := by
          rw [conjSub_conjSub_six9, show g * (g⁻¹ * y * g) = y * g by group, ← conjSub_conjSub_six9]
          exact hy
        have h5 := congrArg (conjSub g⁻¹) h4
        rw [conjSub_inv_conjSub, conjSub_inv_conjSub] at h5
        exact h5
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact h3
    · change (MulEquiv.toMonoidHom (MulAut.conj g)) (g⁻¹ * y * g) = y
      rw [conj_toMonoidHom_apply]; group
  · intro y hy
    obtain ⟨m, hm, hmr⟩ := Subgroup.mem_map.mp hy
    rw [← hmr, Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [map_toMonoidHom_coe (MulAut.conj g) E]
    have hm' : E.map (MulAut.conj m : G →* G) = E :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hm
    rw [show MulEquiv.toMonoidHom (MulAut.conj g) m = g * m * g⁻¹ from
      conj_toMonoidHom_apply g m]
    rw [map_conj_conj, show g * m * g⁻¹ * g = g * m by group, ← map_conj_conj, hm']

/-- A conjugate of a quasisimple subgroup is quasisimple. -/
theorem isQuasisimple_conjSub {E : Subgroup G} (g : G) (h : IsQuasisimple E) :
    IsQuasisimple (conjSub g E) :=
  isQuasisimple_map (MulAut.conj g).toMonoidHom (MulAut.conj g).injective h

variable {G : Type} [Group G] [Finite G]

/-- `N_G(E(M)) = M` for a `Case2Data` (the §4 maximal subgroup `M` with `t ∈ E(M)`): `M`
normalises `E := layerIn M`, `E ≠ ⊥` (it contains `t`, of order `2`), `E ≤ M < ⊤`, so
`N_G(E) ≠ ⊤` and maximality of the coatom `M` gives `N_G(E) = M`. -/
theorem normalizer_layerIn_eq_data {B : BenderSetup G} (hbc : BenderCtx G) (D : Case2Data B) :
    Subgroup.normalizer ((layerIn D.M : Subgroup G) : Set G) = D.M := by
  haveI : IsSimpleGroup G := hbc.simple
  set E : Subgroup G := layerIn D.M with hE
  have hME : D.M ≤ Subgroup.normalizer (E : Set G) := by
    rw [hE]; exact layerIn_le_normalizer D.M
  have hEbot : E ≠ ⊥ := by
    intro hbot
    have ht : B.t ∈ E := by rw [hE]; exact D.t_mem
    rw [hbot] at ht
    simp only [Subgroup.mem_bot] at ht
    have h2 : orderOf B.t = 1 := by rw [ht]; simp
    exact absurd (h2.symm.trans B.t_order) (by norm_num)
  have hEDM : E ≤ D.M := by rw [hE]; exact layerIn_le D.M
  have hEtop : E ≠ ⊤ := fun htop => D.M_coatom.ne_top (top_le_iff.mp (htop ▸ hEDM))
  have hNtop : Subgroup.normalizer (E : Set G) ≠ ⊤ := by
    intro htop
    have hnorm : E.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      exact eq_top_iff.mpr htop.ge
    rcases hnorm.eq_bot_or_eq_top with hb | ht
    · exact hEbot hb
    · exact hEtop ht
  have hNle : Subgroup.normalizer (E : Set G) ≤ D.M := by
    by_contra hcon
    have hne : D.M ≠ Subgroup.normalizer (E : Set G) := fun hh => hcon (le_of_eq hh.symm)
    have hlt : D.M < Subgroup.normalizer (E : Set G) := lt_of_le_of_ne hME hne
    exact hNtop (D.M_coatom.2 _ hlt)
  exact le_antisymm hNle hME

/-- **`C_G(E(M)) ≤ M`.**  `E := layerIn M` is normal in the coatom `M`, nontrivial, and `C_G(E)`
centralises `E`, hence normalises it.  So `K := M ⊔ C_G(E) ≤ N_G(E)`; if `K = ⊤` then `E ⊴ G`,
which contradicts simplicity (`E ≠ ⊥`, `E ≤ M < ⊤`).  Hence `K ≠ ⊤` and maximality of `M` gives
`K = M`, i.e. `C_G(E) ≤ M`.

Note: since `F ≤ C_G(E)`, this does **not** give `C_G(X) ≤ M` for a proper `X < F`: two subgroups
of `C_G(E)` need not commute with each other, and the corresponding statement for `1 ≠ X ≤ F` is
equivalent to the `F`-TI property itself (see the notes). -/
theorem centralizer_layerIn_le {B : BenderSetup G} (hbc : BenderCtx G) (D : Case2Data B) :
    Subgroup.centralizer ((layerIn D.M : Subgroup G) : Set G) ≤ D.M := by
  classical
  haveI : IsSimpleGroup G := hbc.simple
  set E : Subgroup G := layerIn D.M with hE
  have hE_le_M : E ≤ D.M := by rw [hE]; exact layerIn_le D.M
  have hM_le_NE : D.M ≤ Subgroup.normalizer (E : Set G) := by
    rw [hE]; exact layerIn_le_normalizer D.M
  have hK_le : D.M ⊔ Subgroup.centralizer (E : Set G) ≤ Subgroup.normalizer (E : Set G) :=
    sup_le hM_le_NE (Subgroup.centralizer_le_normalizer (E : Set G))
  have hK_ne_top : D.M ⊔ Subgroup.centralizer (E : Set G) ≠ ⊤ := by
    intro htop
    have htop' : (⊤ : Subgroup G) ≤ Subgroup.normalizer (E : Set G) := by
      rw [← htop]; exact hK_le
    have hEnum : E.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      exact eq_top_iff.mpr htop'
    rcases hEnum.eq_bot_or_eq_top with hb | ht
    · have ht_mem : B.t ∈ E := by rw [hE]; exact D.t_mem
      rw [hb] at ht_mem
      have h1 : orderOf B.t = 1 := by rw [Subgroup.mem_bot.mp ht_mem]; simp
      exact absurd (h1.symm.trans B.t_order) (by norm_num)
    · exact D.M_coatom.ne_top (top_le_iff.mp (ht ▸ hE_le_M))
  have hK_eq : D.M ⊔ Subgroup.centralizer (E : Set G) = D.M := by
    by_contra hne
    exact hK_ne_top (D.M_coatom.2 _ (lt_of_le_of_ne le_sup_left (Ne.symm hne)))
  exact le_sup_right.trans (le_of_eq hK_eq)

/-! ## The gap

The two statements below are the *engine* of Bender §4 (6) — "for `1 ≠ X ≤ F` the centralizer, and
then the normalizer, of `X` lies in `M`".  They are **not** derivable from `Case2Pre` +
`Case2PrePlus` as recorded (see `Submission/Work/CORE4/NOTES_CASE2SIX9.md`); they are left here as
statements so that the missing input is visible.  The route Bender uses is Lemma 2.7 applied to
`N_G(X)` (p. 225), which in the formalisation `Work.GW2.Lemma27Prop` requires — besides
`M ≠ ⊤`, `BRel Ĥ M`, `t ∈ M`, `t ∉ E(M)`, non-cyclic Sylow 2-subgroups of `M` and the disjunct
`8 ≤ |S ∩ M| ∨ |S| = 4 ∨ t ∈ O²(M)` — the hypothesis `¬ M ≤ B.Hhat`; for
`M := N_G(X)` (or any coatom containing it and `M`) this last clause is not a consequence of the
recorded hypotheses. -/

/-- **Bender §4 (6), auxiliary (GAP).**  For `1 ≠ X ≤ F`, the centralizer of `X` lies in `M`. -/
theorem centralizer_le_of_le_F (hbc : BenderCtx G) {B : BenderSetup G} (D : Case2Data B)
    (hpre : Case2Pre B D) (X : Subgroup G) (hXne : X ≠ ⊥) (hXF : X ≤ D.F) :
    Subgroup.centralizer (X : Set G) ≤ D.M := by sorry

/-- **Bender §4 (6), first half (GAP).**  `F ∩ F^g = 1` for every `g ∉ M`. -/
theorem ti_F_of_case2pre (I : Work.GW2.C4Inputs) (hbc : BenderCtx G) {B : BenderSetup G}
    (D : Case2Data B) (hpre : Case2Pre B D) :
    ∀ g : G, g ∉ D.M → D.F ⊓ conjSub g D.F = ⊥ := by sorry

/-- **§4 (6), design-pass-9 form** (`Case2SixImpl9`): from `Case2Pre B D` (§4 (1)–(5)) **and**
`Case2PrePlus B D` (Bender's Sylow choice `S ∩ M ∈ Syl₂(M)` and (1),(2)), conclude

    (∀ g : G, g ∉ D.M → D.F ⊓ conjSub g D.F = ⊥) ∧ IsCyclic D.F

i.e. Bender p. 225: "This implies `F ∩ F^g = 1` for each `g ∈ G − M`.  As we can choose
`g ∈ N_H(K₀F)`, `F` is isomorphic to a subgroup of `K₀`, hence `F` is cyclic."

**Status (see `Submission/Work/CORE4/NOTES_CASE2SIX9.md`).**  The statement is *not* derivable from
its hypotheses: the conclusion is equivalent to `N_G(X) ≤ M` for `1 ≠ X ≤ F`, and the recorded data
(`Case2Pre`, `Case2PrePlus`, `BenderCtx`, `C4Inputs`) do not constrain `N_G(X)` for a proper
`X < F` — Bender's own proof of it is Lemma 2.7 applied to `N_G(X)`, whose hypothesis
`N_G(X) ≰ Ĥ` is not available here.  What *is* available is proved in this file
(`N_G(E(M)) = M`, `C_G(E(M)) ≤ M`, the `conjSub` calculus) and in
`Submission/Work/CORE4/Case2Six9Aux/` (the witness `∃ g ∉ M, F^g ≤ F(U) ⊓ M`, and `F` cyclic from
that witness together with the TI property). -/
theorem Case2Six9 (I : Work.GW2.C4Inputs) : Work.GW2.Case2SixImpl9 I := by sorry

end Work.CORE4
