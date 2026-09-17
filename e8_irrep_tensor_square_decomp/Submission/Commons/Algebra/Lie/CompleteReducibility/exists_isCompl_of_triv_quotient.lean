import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open LieSubmodule

namespace Commons.Algebra.Lie.CompleteReducibility

/-!
# Splitting a Lie submodule with trivial quotient

Given a Lie algebra `L` over a field `K` and a finite-dimensional `L`-module `V`, a Lie submodule
`W ≤ V` is said to have *trivial quotient* if `[L, V] ⊆ W` (equivalently, if the quotient `V / W` is
a trivial `L`-module).

The main result `exists_isCompl_of_triv_quotient` shows that if every *irreducible* Lie submodule
`A ≤ V'` with `[L, V'] ⊆ A` (for every finite-dimensional `L`-module `V'`) admits a complement,
then every Lie submodule `W` with trivial quotient admits a complement.

This is the classical reduction in the proof of Weyl's complete reducibility theorem: the simple
case is handled by the Casimir element, while the general case follows by induction on `dim W`,
using a maximal proper submodule `W₀ ⋖ W` and the quotient `V / W₀`.

## Main result

* `Commons.Algebra.Lie.CompleteReducibility.exists_isCompl_of_triv_quotient`
-/

section Helpers

variable {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]

/-- `finrank` strictly increases along strict inclusions of Lie submodules. -/
lemma finrank_lt_of_lt_lieSubmodule [Module.Finite K V]
    {N N' : LieSubmodule K L V} (h : N' < N) : Module.finrank K N' < Module.finrank K N := by
  have hsub : (N' : Submodule K V) < (N : Submodule K V) := by
    refine lt_of_le_of_ne ((LieSubmodule.toSubmodule_le_toSubmodule N' N).mpr h.le) ?_
    intro heq
    exact h.ne (LieSubmodule.toSubmodule_injective heq)
  exact Submodule.finrank_lt_finrank_of_lt (K := K) hsub

/-- The lattice of Lie submodules of a finite-dimensional module is well-founded for the reverse
order, since `finrank` strictly decreases. -/
lemma wellFounded_gt_lieSubmodule [Module.Finite K V] :
    WellFounded ((· > ·) : LieSubmodule K L V → LieSubmodule K L V → Prop) := by
  have hg : ∀ a b : LieSubmodule K L V, a > b →
      (Module.finrank K V - Module.finrank K a) < (Module.finrank K V - Module.finrank K b) := by
    intro a b hab
    have hba : Module.finrank K b < Module.finrank K a := finrank_lt_of_lt_lieSubmodule hab
    have hbV : Module.finrank K b < Module.finrank K V := by
      have hbne : (b : Submodule K V) ≠ ⊤ := by
        intro hbt
        have : b = ⊤ := LieSubmodule.toSubmodule_injective (by simpa using hbt)
        exact (not_le_of_gt hab) (by rw [this]; exact le_top)
      exact Submodule.finrank_lt hbne
    exact Nat.sub_lt_sub_left hbV hba
  exact (InvImage.wf (fun N : LieSubmodule K L V => Module.finrank K V - Module.finrank K N)
    wellFounded_lt).mono hg

/-- Every nonzero Lie submodule of a finite-dimensional module is covered by some strict Lie
submodule, i.e. has a maximal proper Lie submodule. -/
lemma exists_covBy_of_ne_bot [Module.Finite K V]
    (W : LieSubmodule K L V) (hW : W ≠ ⊥) :
    ∃ W₀ : LieSubmodule K L V, W₀ ⋖ W := by
  haveI : IsStronglyCoatomic (LieSubmodule K L V) :=
    IsStronglyCoatomic.of_wellFounded_gt wellFounded_gt_lieSubmodule
  have hlt : (⊥ : Set.Iic W) < ⊤ := by
    rw [Subtype.mk_lt_mk]
    exact bot_lt_iff_ne_bot.mpr hW
  obtain ⟨x, -, hcov⟩ := exists_le_covBy_of_lt (a := (⊥ : Set.Iic W)) (b := ⊤) hlt
  refine ⟨(x : LieSubmodule K L V), ?_⟩
  haveI : IsCoatom x := hcov.isCoatom
  exact (Set.Iic.isCoatom_iff).mp ‹IsCoatom x›

/-- If `W₀ ⋖ W` are Lie submodules then the image of `W` in the quotient `V / W₀` is an
irreducible Lie module. -/
lemma isIrreducible_map_mk'_of_covBy [Module.Finite K V]
    {W₀ W : LieSubmodule K L V} (hcov : W₀ ⋖ W) :
    LieModule.IsIrreducible K L (W.map (LieSubmodule.Quotient.mk' W₀)) := by
  set q : V →ₗ⁅K,L⁆ (V ⧸ W₀) := LieSubmodule.Quotient.mk' W₀ with hq
  set Abar : LieSubmodule K L (V ⧸ W₀) := W.map q with hAbar
  have hAbarne : Abar ≠ ⊥ := by
    intro h
    have hle : W ≤ W₀ := (LieSubmodule.Quotient.map_mk'_eq_bot_le W₀ W).mp h
    exact (not_le_of_gt hcov.lt) hle
  haveI : Nontrivial ↥Abar := by
    rw [nontrivial_iff_ne_bot]
    exact hAbarne
  refine LieModule.IsIrreducible.mk fun N hN => ?_
  have hinj : Function.Injective (Abar.incl) := Subtype.coe_injective
  have hNmap : N.map Abar.incl ≠ ⊥ := by
    intro h
    apply hN
    have hinjmap := LieSubmodule.map_injective_of_injective (f := Abar.incl) hinj
    apply hinjmap
    rw [h, LieSubmodule.map_bot]
  set P : LieSubmodule K L V := (N.map Abar.incl).comap q with hP
  have hrange : q.range = ⊤ :=
    (LieModuleHom.range_eq_top q).mpr (LieSubmodule.Quotient.surjective_mk' W₀)
  have hPmap : P.map q = N.map Abar.incl := by
    rw [hP]
    exact LieSubmodule.map_comap_eq (f := q) (N₂ := N.map Abar.incl)
      (by rw [hrange]; exact le_top)
  have hW₀P : W₀ ≤ P := by
    intro w hw
    rw [hP, LieSubmodule.mem_comap]
    have hqw : q w = 0 := (LieSubmodule.Quotient.mk_eq_zero W₀).mpr hw
    rw [hqw]
    exact (N.map Abar.incl).zero_mem
  have hPW : P ≤ W := by
    intro v hv
    have hvA : q v ∈ Abar := by
      have hmem : q v ∈ N.map Abar.incl := LieSubmodule.mem_comap.mp hv
      exact LieSubmodule.map_incl_le hmem
    rw [hAbar, LieSubmodule.mem_map] at hvA
    obtain ⟨w, hw, hwv⟩ := hvA
    have hvsub : v - w ∈ W₀ := by
      have : q (v - w) = 0 := by rw [map_sub, hwv, sub_self]
      exact (LieSubmodule.Quotient.mk_eq_zero W₀).mp this
    have : v = w + (v - w) := by abel
    rw [this]
    exact W.add_mem hw (hcov.lt.le hvsub)
  have hPne : P ≠ W₀ := by
    intro hP0
    have hbot : N.map Abar.incl = ⊥ := by
      rw [← hPmap, hP0]
      exact (LieSubmodule.Quotient.map_mk'_eq_bot_le W₀ W₀).mpr le_rfl
    exact hNmap hbot
  have hPW' : P = W := by
    rcases lt_or_eq_of_le hPW with hlt | heq
    · exact absurd hlt (hcov.2 (lt_of_le_of_ne hW₀P (Ne.symm hPne)))
    · exact heq
  have hNm : N.map Abar.incl = (⊤ : LieSubmodule K L ↥Abar).map Abar.incl := by
    rw [LieSubmodule.map_incl_top, ← hPmap, hPW']
  exact LieSubmodule.map_injective_of_injective (f := Abar.incl) hinj hNm

end Helpers

theorem exists_isCompl_of_triv_quotient {K : Type*} {L : Type*} [Field K] [LieRing L]
    [LieAlgebra K L]
    (hsimple : ∀ (V : Type) [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
      [Module.Finite K V] (A : LieSubmodule K L V), LieModule.IsIrreducible K L A →
      (∀ (x : L) (v : V), ⁅x, v⁆ ∈ A) → ∃ M : LieSubmodule K L V, IsCompl A M)
    (V : Type) [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [Module.Finite K V] (W : LieSubmodule K L V)
    (htriv : ∀ (x : L) (v : V), ⁅x, v⁆ ∈ W) : ∃ W' : LieSubmodule K L V, IsCompl W W' := by
  classical
  have key : ∀ n : ℕ, ∀ (V' : Type) [AddCommGroup V'] [Module K V'] [LieRingModule L V']
      [LieModule K L V'] [Module.Finite K V'], Module.finrank K V' = n →
      ∀ (W' : LieSubmodule K L V'), (∀ (x : L) (v : V'), ⁅x, v⁆ ∈ W') →
      ∃ W'' : LieSubmodule K L V', IsCompl W' W'' := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V' _ _ _ _ _ hfr W' htriv'
      by_cases hbot : W' = ⊥
      · exact ⟨⊤, by rw [hbot]; exact isCompl_bot_top⟩
      · obtain ⟨W₀, hcov⟩ := exists_covBy_of_ne_bot W' hbot
        have hW₀lt : W₀ < W' := hcov.lt
        have hW₀le : W₀ ≤ W' := hW₀lt.le
        set q : V' →ₗ⁅K,L⁆ (V' ⧸ W₀) := LieSubmodule.Quotient.mk' W₀ with hq
        set Abar : LieSubmodule K L (V' ⧸ W₀) := W'.map q with hAbar
        haveI hAbarir : LieModule.IsIrreducible K L Abar := by
          rw [hAbar, hq]
          exact isIrreducible_map_mk'_of_covBy hcov
        have htrivAbar : ∀ (x : L) (y : V' ⧸ W₀), ⁅x, y⁆ ∈ Abar := by
          intro x y
          obtain ⟨v, rfl⟩ := LieSubmodule.Quotient.surjective_mk' W₀ y
          rw [← LieModuleHom.map_lie, hAbar]
          exact LieSubmodule.mem_map_of_mem (htriv' x v)
        obtain ⟨B, hB⟩ := hsimple (V' ⧸ W₀) Abar hAbarir htrivAbar
        set Q : LieSubmodule K L V' := B.comap q with hQ
        have hWQ : W' ⊓ Q = W₀ := by
          apply le_antisymm
          · intro v hv
            rw [LieSubmodule.mem_inf] at hv
            obtain ⟨hvW, hvQ⟩ := hv
            have hvB : q v ∈ B := LieSubmodule.mem_comap.mp hvQ
            have hvA : q v ∈ Abar := by
              rw [hAbar]
              exact LieSubmodule.mem_map_of_mem hvW
            have : q v ∈ Abar ⊓ B := (LieSubmodule.mem_inf Abar B (q v)).mpr ⟨hvA, hvB⟩
            rw [hB.inf_eq_bot, LieSubmodule.mem_bot] at this
            exact (LieSubmodule.Quotient.mk_eq_zero W₀).mp this
          · intro v hv
            refine (LieSubmodule.mem_inf W' Q v).mpr ⟨hW₀le hv, ?_⟩
            rw [LieSubmodule.mem_comap]
            have : q v = 0 := (LieSubmodule.Quotient.mk_eq_zero W₀).mpr hv
            rw [this]
            exact B.zero_mem
        have hVQ : W' ⊔ Q = ⊤ := by
          rw [eq_top_iff]
          intro v _
          have hv : q v ∈ Abar ⊔ B := by rw [hB.sup_eq_top]; trivial
          rw [LieSubmodule.mem_sup] at hv
          obtain ⟨a, ha, b, hb, hab⟩ := hv
          have ha' : a ∈ W'.map q := by rwa [hAbar] at ha
          rw [LieSubmodule.mem_map] at ha'
          obtain ⟨w, hw, hwv⟩ := ha'
          rw [LieSubmodule.mem_sup]
          refine ⟨w, hw, v - w, ?_, by abel⟩
          rw [LieSubmodule.mem_comap]
          have hqw : q (v - w) = b := by rw [map_sub, hwv]; rw [← hab]; abel
          rw [hqw]
          exact hb
        have hW₀Q : W₀ ≤ Q := by rw [← hWQ]; exact inf_le_right
        have hAbarne : Abar ≠ ⊥ := by
          intro h
          have hle : W' ≤ W₀ := (LieSubmodule.Quotient.map_mk'_eq_bot_le W₀ W').mp h
          exact (not_le_of_gt hW₀lt) hle
        have hQne : Q ≠ ⊤ := by
          intro hQtop
          have hBtop : B = ⊤ := by
            rw [eq_top_iff]
            intro y _
            obtain ⟨v, rfl⟩ := LieSubmodule.Quotient.surjective_mk' W₀ y
            have hv : v ∈ Q := by rw [hQtop]; trivial
            exact LieSubmodule.mem_comap.mp hv
          have hAbot : Abar = ⊥ := by
            rw [← hB.inf_eq_bot, hBtop, inf_top_eq]
          exact hAbarne hAbot
        have hQne' : (Q : Submodule K V') ≠ ⊤ := by
          intro h
          exact hQne (LieSubmodule.toSubmodule_injective (by rw [h, LieSubmodule.top_toSubmodule]))
        have hQlt : Module.finrank K ↥Q < n := by
          have := Submodule.finrank_lt (K := K) (V := V') hQne'
          rw [hfr] at this
          exact this
        let W₀' : LieSubmodule K L ↥Q := W₀.comap Q.incl
        have htrivQ : ∀ (x : L) (v : ↥Q), ⁅x, v⁆ ∈ W₀' := by
          intro x v
          rw [show W₀' = W₀.comap Q.incl from rfl, LieSubmodule.mem_comap,
            LieModuleHom.map_lie]
          have h1 : ⁅x, (v : V')⁆ ∈ W' := htriv' x (v : V')
          have h2 : ⁅x, (v : V')⁆ ∈ Q := Q.lie_mem v.2
          have h3 : ⁅x, (v : V')⁆ ∈ W' ⊓ Q :=
            (LieSubmodule.mem_inf W' Q ⁅x, (v : V')⁆).mpr ⟨h1, h2⟩
          rw [hWQ] at h3
          exact h3
        obtain ⟨M', hM'⟩ := ih (Module.finrank K ↥Q) hQlt ↥Q rfl W₀' htrivQ
        have hW₀map : W₀'.map Q.incl = W₀ := by
          rw [show W₀' = W₀.comap Q.incl from rfl,
            LieSubmodule.map_comap_incl Q W₀, inf_eq_right.mpr hW₀Q]
        have hW₀M : W₀ ⊓ (M'.map Q.incl) = ⊥ := by
          have h := congrArg (LieSubmodule.map Q.incl) hM'.inf_eq_bot
          rw [LieSubmodule.map_inf (f := Q.incl) Subtype.coe_injective, LieSubmodule.map_bot,
            hW₀map] at h
          exact h
        have hW₀sup : W₀ ⊔ (M'.map Q.incl) = Q := by
          have h := congrArg (LieSubmodule.map Q.incl) hM'.sup_eq_top
          rw [LieSubmodule.map_sup, LieSubmodule.map_incl_top, hW₀map] at h
          exact h
        refine ⟨M'.map Q.incl, ?_⟩
        have hMleQ : M'.map Q.incl ≤ Q := LieSubmodule.map_incl_le
        have hinf : W' ⊓ (M'.map Q.incl) = ⊥ := by
          refine le_antisymm ?_ bot_le
          have h4 : W' ⊓ (M'.map Q.incl) ≤ W₀ ⊓ (M'.map Q.incl) :=
            le_inf (hWQ ▸ inf_le_inf_left W' hMleQ) inf_le_right
          rwa [hW₀M] at h4
        have hsup : W' ⊔ (M'.map Q.incl) = ⊤ := by
          have hWM : W' ⊔ Q = W' ⊔ (M'.map Q.incl) := by
            conv_lhs => rw [← hW₀sup]
            rw [← sup_assoc, sup_eq_left.mpr hW₀le]
          rw [← hWM, hVQ]
        exact isCompl_iff.mpr ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩
  exact key (Module.finrank K V) V rfl W htriv

end Commons.Algebra.Lie.CompleteReducibility