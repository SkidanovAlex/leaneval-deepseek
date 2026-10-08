import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Existence of a simple subrepresentation on which a subgroup acts non-trivially

Given a semisimple representation `ρ` of a group `G` on a finite-dimensional `k`-vector space `V`
and a subgroup `K ≤ G` which is *not* contained in `ker ρ`, there is an irreducible
subrepresentation `W ≤ ρ` on which `K` still acts non-trivially.
-/

namespace Work.CharPrelim

section Helpers

variable {k : Type*} [Field k] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module k V]

lemma map_subtype_eq_bot_iff {p : Submodule k V} {q : Submodule k ↥p} :
    q.map p.subtype = ⊥ ↔ q = ⊥ := by
  constructor
  · intro h
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hmem : (x : V) ∈ (⊥ : Submodule k V) := by
      rw [← h]; exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    have hx0 : (x : V) = 0 := by simpa using hmem
    exact p.subtype_injective (by simpa using hx0)
  · rintro rfl; simp

lemma map_subtype_eq_self_iff {p : Submodule k V} {q : Submodule k ↥p} :
    q.map p.subtype = p ↔ q = ⊤ := by
  constructor
  · intro h
    rw [Submodule.eq_top_iff']
    intro x
    have : (x : V) ∈ q.map p.subtype := by rw [h]; exact x.2
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp this
    rwa [p.subtype_injective hyx] at hy
  · rintro rfl
    simp

def Subrepresentation.mapIncl (ρ : Representation k G V) (W : Subrepresentation ρ)
    (U : Subrepresentation W.toRepresentation) : Subrepresentation ρ where
  toSubmodule := U.toSubmodule.map W.toSubmodule.subtype
  apply_mem_toSubmodule g v hv := by
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
    refine Submodule.mem_map.mpr ⟨W.toRepresentation g u, U.apply_mem_toSubmodule g hu, ?_⟩
    rfl

lemma Subrepresentation.mapIncl_le (ρ : Representation k G V) (W : Subrepresentation ρ)
    (U : Subrepresentation W.toRepresentation) : Subrepresentation.mapIncl ρ W U ≤ W :=
  Submodule.map_subtype_le _ _

lemma Subrepresentation.mapIncl_eq_bot_iff (ρ : Representation k G V) (W : Subrepresentation ρ)
    (U : Subrepresentation W.toRepresentation) :
    Subrepresentation.mapIncl ρ W U = ⊥ ↔ U = ⊥ := by
  rw [show (Subrepresentation.mapIncl ρ W U = ⊥) ↔
      (Subrepresentation.mapIncl ρ W U).toSubmodule = (⊥ : Subrepresentation ρ).toSubmodule from
    ⟨fun h => congrArg _ h, fun h => Subrepresentation.ext h⟩]
  show U.toSubmodule.map W.toSubmodule.subtype = ⊥ ↔ U = ⊥
  rw [map_subtype_eq_bot_iff]
  exact ⟨fun h => Subrepresentation.ext h, fun h => congrArg _ h⟩

lemma Subrepresentation.mapIncl_eq_self_iff (ρ : Representation k G V) (W : Subrepresentation ρ)
    (U : Subrepresentation W.toRepresentation) :
    Subrepresentation.mapIncl ρ W U = W ↔ U = ⊤ := by
  rw [show (Subrepresentation.mapIncl ρ W U = W) ↔
      (Subrepresentation.mapIncl ρ W U).toSubmodule = W.toSubmodule from
    ⟨fun h => congrArg _ h, fun h => Subrepresentation.ext h⟩]
  show U.toSubmodule.map W.toSubmodule.subtype = W.toSubmodule ↔ U = ⊤
  rw [map_subtype_eq_self_iff]
  exact ⟨fun h => Subrepresentation.ext h, fun h => congrArg _ h⟩

lemma isIrreducible_toRepresentation_of_isAtom (ρ : Representation k G V) (W : Subrepresentation ρ)
    (hW : IsAtom W) : Representation.IsIrreducible W.toRepresentation := by
  have : Nontrivial (Subrepresentation W.toRepresentation) := by
    refine ⟨⊥, ⊤, fun h => hW.1 ?_⟩
    have hsub : (⊥ : Submodule k ↥W.toSubmodule) = ⊤ := congrArg Subrepresentation.toSubmodule h
    have hsubsing : Subsingleton ↥W.toSubmodule :=
      ⟨fun x y => by
        have hx : x ∈ (⊥ : Submodule k ↥W.toSubmodule) := by rw [hsub]; exact Submodule.mem_top
        have hy : y ∈ (⊥ : Submodule k ↥W.toSubmodule) := by rw [hsub]; exact Submodule.mem_top
        rw [Submodule.mem_bot] at hx hy
        rw [hx, hy]⟩
    have hbot : W.toSubmodule = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.mem_bot]
      exact congrArg Subtype.val (hsubsing.elim (⟨x, hx⟩ : ↥W.toSubmodule) 0)
    exact Subrepresentation.ext hbot
  refine ⟨fun U => ?_⟩
  by_cases h : Subrepresentation.mapIncl ρ W U = ⊥
  · left; exact (Subrepresentation.mapIncl_eq_bot_iff ρ W U).mp h
  · right
    have hle := Subrepresentation.mapIncl_le ρ W U
    have hself : Subrepresentation.mapIncl ρ W U = W := by
      by_contra hne
      exact h (hW.2 _ (lt_of_le_of_ne hle hne))
    exact (Subrepresentation.mapIncl_eq_self_iff ρ W U).mp hself

end Helpers

theorem exists_simple_subrepresentation_nontrivial {k : Type*} [Field k] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) [Representation.IsSemisimpleRepresentation ρ]
    (K : Subgroup G) (h : ¬ K ≤ ρ.ker) :
    ∃ W : Subrepresentation ρ,
      Representation.IsIrreducible W.toRepresentation ∧ ¬ K ≤ W.toRepresentation.ker := by
  classical
  obtain ⟨g, hgK, hgker⟩ : ∃ g ∈ K, g ∉ ρ.ker := by
    by_contra hc
    simp only [not_exists, not_and, not_not] at hc
    exact h fun x hx => hc x hx
  have hg1 : ρ g ≠ 1 := fun hcon => hgker (MonoidHom.mem_ker.mpr hcon)
  obtain ⟨v₀, hv₀⟩ : ∃ v, ρ g v ≠ v := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hg1 (LinearMap.ext hc)
  have hex : ∃ n, ∃ W : Subrepresentation ρ, (∃ v ∈ W.toSubmodule, ρ g v ≠ v) ∧
      Module.finrank k W.toSubmodule = n :=
    ⟨_, ⊤, ⟨v₀, Submodule.mem_top, hv₀⟩, rfl⟩
  obtain ⟨W, hWmem, hWfin⟩ := Nat.find_spec hex
  have hmin : ∀ W' : Subrepresentation ρ, (∃ v ∈ W'.toSubmodule, ρ g v ≠ v) →
      W' ≤ W → W' = W := by
    intro W' hW' hle
    have h1 : Nat.find hex ≤ Module.finrank k W'.toSubmodule :=
      Nat.find_min' hex ⟨W', hW', rfl⟩
    have h2 : Module.finrank k W'.toSubmodule ≤ Module.finrank k W.toSubmodule :=
      Submodule.finrank_mono hle
    have h3 : Module.finrank k W'.toSubmodule = Module.finrank k W.toSubmodule := by
      rw [hWfin] at h2 ⊢
      exact le_antisymm h2 h1
    exact Subrepresentation.ext (Submodule.eq_of_le_of_finrank_eq hle h3)
  have hWne : W ≠ ⊥ := by
    rintro hbot
    obtain ⟨v, hv, hvne⟩ := hWmem
    rw [hbot] at hv
    change v ∈ (⊥ : Submodule k V) at hv
    have hv0 : v = 0 := by simpa using hv
    exact hvne (by rw [hv0]; simp)
  have hatom : IsAtom W := ⟨hWne, fun b hb => by
    have hbW : b ≤ W := le_of_lt hb
    by_cases hbS : ∃ v ∈ b.toSubmodule, ρ g v ≠ v
    · exact absurd (hmin b hbS hbW) (ne_of_lt hb)
    · simp only [not_exists, not_and, not_not] at hbS
      obtain ⟨b', hcompl⟩ := exists_isCompl b
      have hWb'S : ∃ v ∈ (W ⊓ b').toSubmodule, ρ g v ≠ v := by
        by_contra hcon
        simp only [not_exists, not_and, not_not] at hcon
        obtain ⟨v, hvW, hvne⟩ := hWmem
        have hmem : v ∈ (b ⊔ b').toSubmodule := by
          rw [hcompl.sup_eq_top]; exact Submodule.mem_top
        rw [Subrepresentation.toSubmodule_sup] at hmem
        obtain ⟨a, ha, a', ha', haa'⟩ := Submodule.mem_sup.mp hmem
        have haW : a ∈ W.toSubmodule := hbW ha
        have ha'W : a' ∈ W.toSubmodule := by
          have heq : a' = v - a := by rw [← haa']; abel
          rw [heq]; exact Submodule.sub_mem _ hvW haW
        have h1 : ρ g a = a := hbS a ha
        have h2 : ρ g a' = a' := hcon a' (Submodule.mem_inf.mpr ⟨ha'W, ha'⟩)
        exact hvne (by rw [← haa', map_add, h1, h2])
      have : W ⊓ b' = W := hmin (W ⊓ b') hWb'S inf_le_left
      have hWb' : W ≤ b' := by rw [← this]; exact inf_le_right
      have hbb' : b ≤ b' := hbW.trans hWb'
      have h2 : b = b ⊓ b' := (inf_eq_left.mpr hbb').symm
      rw [h2, hcompl.inf_eq_bot]⟩
  refine ⟨W, isIrreducible_toRepresentation_of_isAtom ρ W hatom, ?_⟩
  intro hK
  have hker : g ∈ W.toRepresentation.ker := hK hgK
  rw [MonoidHom.mem_ker] at hker
  obtain ⟨v, hv, hvne⟩ := hWmem
  have h1 : W.toRepresentation g ⟨v, hv⟩ = ⟨v, hv⟩ := by rw [hker]; rfl
  have h2 : ρ g v = v := by
    have hh := congrArg Subtype.val h1
    simpa [Subrepresentation.toRepresentation] using hh
  exact hvne h2

end Work.CharPrelim
