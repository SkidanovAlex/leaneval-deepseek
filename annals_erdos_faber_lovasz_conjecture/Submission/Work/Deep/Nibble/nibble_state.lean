import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.nibble_defs

/-!
# The state of the Rödl-nibble iteration

Vocabulary for iterating the one-round lemma `Work.Deep.Nibble.nibble_round2`
(`Submission/Work/Deep/Nibble/nibble_round2.lean`), together with the basic
transfer lemmas between a hypergraph `𝓗 : Set (Set (Fin n))` and its restriction
to a vertex set `U : Set (Fin n)`.

The iteration keeps track only of the uncovered vertex set `U`: the hypergraph of
the current round is `res 𝓗 U`, the family of edges of `𝓗` lying inside `U`
transported to the subtype `↥U` (so that `nibble_round2` applies to it).  The
degrees of `res 𝓗 U` at `v : ↥U` are `deg 𝓗 U v`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Nibble

variable {n : ℕ}

/-- The edges of `𝓗` lying inside `U`, as a family on the subtype `↥U`. -/
noncomputable def res (𝓗 : Set (Set (Fin n))) (U : Set (Fin n)) : Set (Set ↥U) :=
  {e | (Subtype.val '' e : Set (Fin n)) ∈ 𝓗}

/-- The edges of `𝓗` lying inside `U`, as subsets of `Fin n`. -/
def fam (𝓗 : Set (Set (Fin n))) (U : Set (Fin n)) : Set (Set (Fin n)) :=
  {s | s ⊆ U ∧ s ∈ 𝓗}

/-- The edges of `𝓗` lying inside `U` and through `v`, as a set of sets. -/
def star (𝓗 : Set (Set (Fin n))) (U : Set (Fin n)) (v : Fin n) : Set (Set (Fin n)) :=
  {s | s ⊆ U ∧ s ∈ 𝓗 ∧ v ∈ s}

/-- The number of edges of `𝓗` through `v` that lie inside `U`. -/
noncomputable def deg (𝓗 : Set (Set (Fin n))) (U : Set (Fin n)) (v : Fin n) : ℕ :=
  (star 𝓗 U v).ncard

variable {𝓗 : Set (Set (Fin n))} {U : Set (Fin n)}

theorem mem_res {e : Set ↥U} : e ∈ res 𝓗 U ↔ (Subtype.val '' e : Set (Fin n)) ∈ 𝓗 := Iff.rfl

theorem mem_fam {s : Set (Fin n)} : s ∈ fam 𝓗 U ↔ s ⊆ U ∧ s ∈ 𝓗 := Iff.rfl

theorem mem_star {s : Set (Fin n)} {v : Fin n} :
    s ∈ star 𝓗 U v ↔ s ⊆ U ∧ s ∈ 𝓗 ∧ v ∈ s := Iff.rfl

theorem deg_eq_star_ncard (v : Fin n) : deg 𝓗 U v = (star 𝓗 U v).ncard := rfl

theorem star_subset_fam (v : Fin n) : star 𝓗 U v ⊆ fam 𝓗 U := fun s hs => ⟨hs.1, hs.2.1⟩

theorem fam_subset : fam 𝓗 U ⊆ 𝓗 := fun s hs => hs.2

theorem fam_mono {U' : Set (Fin n)} (h : U' ⊆ U) : fam 𝓗 U' ⊆ fam 𝓗 U :=
  fun s hs => ⟨hs.1.trans h, hs.2⟩

/-- The image of a family on `↥U` under `Subtype.val` determines it. -/
theorem valn_injective :
    Function.Injective (fun e : Set ↥U => (Subtype.val '' e : Set (Fin n))) :=
  Set.image_injective.mpr Subtype.val_injective

/-- Cardinalities are preserved when a family on `↥U` is viewed in `Fin n`. -/
theorem ncard_valn (e : Set ↥U) : (Subtype.val '' e : Set (Fin n)).ncard = e.ncard :=
  Set.ncard_image_of_injective e Subtype.val_injective

/-- The restriction of `𝓗` to `U` is exactly `fam 𝓗 U`, as subsets of `Fin n`. -/
theorem image_val_res : (fun e : Set ↥U => (Subtype.val '' e : Set (Fin n))) '' res 𝓗 U
    = fam 𝓗 U := by
  ext s
  constructor
  · rintro ⟨e, he, rfl⟩
    refine ⟨fun x hx => ?_, he⟩
    obtain ⟨y, hy, rfl⟩ := hx
    exact y.2
  · rintro ⟨hsub, hs⟩
    have hkey : ((Subtype.val : ↥U → Fin n) '' ((Subtype.val : ↥U → Fin n) ⁻¹' s)) = s := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨⟨x, hsub hx⟩, hx, rfl⟩
    refine ⟨(Subtype.val : ↥U → Fin n) ⁻¹' s, ?_, hkey⟩
    show ((Subtype.val : ↥U → Fin n) '' ((Subtype.val : ↥U → Fin n) ⁻¹' s)) ∈ 𝓗
    rw [hkey]
    exact hs

/-- `res 𝓗 U` is uniform whenever `𝓗` is. -/
theorem res_unif {r : ℕ} (h : HUnif 𝓗 r) : HUnif (res 𝓗 U) r := by
  intro e he
  rw [← ncard_valn (U := U) e]
  exact h _ he

/-- `res 𝓗 U` is linear whenever `𝓗` is. -/
theorem res_linear (h : HLin 𝓗) : HLin (res 𝓗 U) := by
  intro e he f hf hne x hx y hy
  have himg : (Subtype.val '' e : Set (Fin n)) ≠ (Subtype.val '' f : Set (Fin n)) :=
    fun hc => hne (valn_injective hc)
  have hpair := h he hf himg
  have hx' : (x : Fin n) ∈ (Subtype.val '' e : Set (Fin n)) ∩ (Subtype.val '' f : Set (Fin n)) :=
    ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
  have hy' : (y : Fin n) ∈ (Subtype.val '' e : Set (Fin n)) ∩ (Subtype.val '' f : Set (Fin n)) :=
    ⟨⟨y, hy.1, rfl⟩, ⟨y, hy.2, rfl⟩⟩
  exact Subtype.val_injective (hpair hx' hy')

/-- `fam 𝓗 U` is linear whenever `𝓗` is. -/
theorem fam_linear (hl : HLin 𝓗) : HLin (fam 𝓗 U) :=
  fun e he f hf hne => hl (fam_subset he) (fam_subset hf) hne

/-- `fam 𝓗 U` is uniform whenever `𝓗` is. -/
theorem fam_unif {r : ℕ} (hu : HUnif 𝓗 r) : HUnif (fam 𝓗 U) r :=
  fun e he => hu e (fam_subset he)

end Work.Deep.Nibble
