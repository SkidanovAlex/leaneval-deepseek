import Mathlib
import Submission.Work.Drive.TripleGeneral

/-!
# From the transversality of three sweeps to the regularity of their plane class maps

The design's *block criterion* (`Work.Drive.tripleTransverseE_of_blocks`) says: for three plane class
derivatives `c k : ℝ² →L ℝ³` that are injective with `range c₀ ⊓ range c₁ ⊓ range c₂ = ⊥`, the three
block maps `f k = ((b k) ∘ π + (a k) • τ) × ((c k) ∘ π) : ℝ³ → ℝ × ℝ³` are in general position.

This file proves the **converse extraction**, which is what turns the *design's* `Meet3Hyp` (an
intrinsic transversality statement) into the *class-level* regularity consumed by the ends clause
(`Work.Drive.PairReg`, `Work.Drive.EndTripleReg`):

* `Work.Drive.inj_inf_of_tripleTransverseE_of_blocks`: if the second component of every block `f k` is
  `(c k) ∘ π` with `π` onto, then general position of the blocks forces each `c k` to be injective and
  the three ranges to meet in `⊥`.

The mechanism is the one of `Work.Drive.not_tripleTransverseE_of_blocks_of_not_injective`: the second
components of the two difference equations form the linear map

> `L (y₀,y₁,y₂) = (c₀y₀ - c₁y₁, c₀y₀ - c₂y₂) : ℝ⁶ → ℝ⁶`,

which is onto because it is the second-component projection of the (surjective) block difference map,
and hence injective by dimension counting; and the value of `L` on a triple with a kernel vector of any
one `c k` gives injectivity of that `c k`, while its value on a common range vector gives the range
intersection.
-/

namespace Work.Drive

open scoped Manifold ContDiff

noncomputable section

/-- The plane parameter space of a presentation. -/
abbrev Tgt2 := EuclideanSpace ℝ (Fin 2)

/-- The plane parameter space `ℝ²` and the projective model `ℝ³`, both of them Euclidean spaces; the
abbreviations keep the statements of this file readable. -/
abbrev Tgt3 := EuclideanSpace ℝ (Fin 3)

/-! ## 1. The difference map of three plane derivatives -/

/-- The first coordinate of a triple of plane parameter vectors. -/
def sqProj0 : (Tgt2 × Tgt2 × Tgt2) →L[ℝ] Tgt2 := ContinuousLinearMap.fst ℝ _ _

/-- The second coordinate of a triple of plane parameter vectors. -/
def sqProj1 : (Tgt2 × Tgt2 × Tgt2) →L[ℝ] Tgt2 :=
  (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)

/-- The third coordinate of a triple of plane parameter vectors. -/
def sqProj2 : (Tgt2 × Tgt2 × Tgt2) →L[ℝ] Tgt2 :=
  (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)

@[simp] lemma sqProj0_apply (v : Tgt2 × Tgt2 × Tgt2) : sqProj0 v = v.1 := rfl
@[simp] lemma sqProj1_apply (v : Tgt2 × Tgt2 × Tgt2) : sqProj1 v = v.2.1 := rfl
@[simp] lemma sqProj2_apply (v : Tgt2 × Tgt2 × Tgt2) : sqProj2 v = v.2.2 := rfl

/-- **The difference map of three plane derivatives**: `(a₀,a₁,a₂) ↦ (A₀a₀ - A₁a₁, A₀a₀ - A₂a₂)`. -/
def tripleDiffLM2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Fin 3 → Tgt2 →L[ℝ] E) : (Tgt2 × Tgt2 × Tgt2) →L[ℝ] E × E :=
  ((A 0).comp sqProj0 - (A 1).comp sqProj1).prod ((A 0).comp sqProj0 - (A 2).comp sqProj2)

@[simp] lemma tripleDiffLM2_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Fin 3 → Tgt2 →L[ℝ] E) (v : Tgt2 × Tgt2 × Tgt2) :
    tripleDiffLM2 A v = (A 0 v.1 - A 1 v.2.1, A 0 v.1 - A 2 v.2.2) := rfl

lemma finrank_Tgt2 : Module.finrank ℝ Tgt2 = 2 := by simp

/-- **Surjectivity of the plane difference map forces it to be injective** (whether or not the three
planes are in general position): domain and target are both `6`-dimensional. -/
lemma tripleDiffLM2_injective_of_surjective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 3) (A : Fin 3 → Tgt2 →L[ℝ] E)
    (h : Function.Surjective (tripleDiffLM2 A)) :
    (∀ k, Function.Injective (A k)) ∧ (A 0).range ⊓ (A 1).range ⊓ (A 2).range = ⊥ := by
  have hdom : Module.finrank ℝ (Tgt2 × Tgt2 × Tgt2) = 6 := by
    rw [Module.finrank_prod, Module.finrank_prod, finrank_Tgt2]
  have hcod : Module.finrank ℝ (E × E) = 6 := by
    rw [Module.finrank_prod, hE]
  have hdim : Module.finrank ℝ (Tgt2 × Tgt2 × Tgt2) = Module.finrank ℝ (E × E) := by
    rw [hdom, hcod]
  have hinj : Function.Injective (tripleDiffLM2 A) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr h
  have key : ∀ v : Tgt2 × Tgt2 × Tgt2, tripleDiffLM2 A v = 0 → v = 0 := by
    intro v hv
    exact hinj (by rw [hv, map_zero])
  have hinj0 : Function.Injective (A 0) := by
    intro a b hab
    have h1 : tripleDiffLM2 A (a - b, 0, 0) = 0 := by
      rw [tripleDiffLM2_apply]
      apply Prod.ext <;> simp [map_sub, hab]
    exact sub_eq_zero.mp (congrArg Prod.fst (key _ h1))
  have hinj1 : Function.Injective (A 1) := by
    intro a b hab
    have h1 : tripleDiffLM2 A (0, a - b, 0) = 0 := by
      rw [tripleDiffLM2_apply]
      apply Prod.ext <;> simp [map_sub, hab]
    exact sub_eq_zero.mp (congrArg (fun t : Tgt2 × Tgt2 × Tgt2 => t.2.1) (key _ h1))
  have hinj2 : Function.Injective (A 2) := by
    intro a b hab
    have h1 : tripleDiffLM2 A (0, 0, a - b) = 0 := by
      rw [tripleDiffLM2_apply]
      apply Prod.ext <;> simp [map_sub, hab]
    exact sub_eq_zero.mp (congrArg (fun t : Tgt2 × Tgt2 × Tgt2 => t.2.2) (key _ h1))
  refine ⟨?_, ?_⟩
  · intro k
    fin_cases k
    · exact hinj0
    · exact hinj1
    · exact hinj2
  · rw [Submodule.eq_bot_iff]
    intro u hu
    obtain ⟨h012, hu12⟩ := Submodule.mem_inf.mp hu
    obtain ⟨h01, h2mem⟩ := Submodule.mem_inf.mp h012
    obtain ⟨a0, ha0⟩ := LinearMap.mem_range.mp h01
    obtain ⟨a1, ha1⟩ := LinearMap.mem_range.mp h2mem
    obtain ⟨a2, ha2⟩ := LinearMap.mem_range.mp hu12
    have ha0' : (A 0) a0 = u := ha0
    have ha1' : (A 1) a1 = u := ha1
    have ha2' : (A 2) a2 = u := ha2
    have h1 : tripleDiffLM2 A (a0, a1, a2) = 0 := by
      change ((A 0) a0 - (A 1) a1, (A 0) a0 - (A 2) a2) = (0 : E × E)
      rw [ha0', ha1', ha2', sub_self]
      rfl
    have h2 : a0 = 0 := congrArg Prod.fst (key _ h1)
    rw [← ha0', h2, map_zero]

/-! ## 2. The converse direction of the block criterion -/

section Blocks

/-- **The class regularity of the blocks from their general position.**

If the second component of every block `f k : ℝ³ →L ℝ × ℝ³` is `(c k) ∘ π` with `π` onto, then the
general position of the three blocks forces every plane class derivative `c k` to be injective and the
three class `2`-planes to meet in `⊥`.  (The first component of the blocks — the level block — is
irrelevant to the conclusion, which is why it does not appear.) -/
theorem inj_inf_of_tripleTransverseE_of_blocks
    (π : Tgt3 →L[ℝ] Tgt2)
    (f : Fin 3 → Tgt3 →L[ℝ] ℝ × Tgt3) (c : Fin 3 → Tgt2 →L[ℝ] Tgt3)
    (hf : ∀ k v, (f k v).2 = c k (π v))
    (h : TripleTransverseE (f 0) (f 1) (f 2)) :
    (∀ k, Function.Injective (c k)) ∧ (c 0).range ⊓ (c 1).range ⊓ (c 2).range = ⊥ := by
  have hsurj : Function.Surjective (tripleDiffLM2 c) := by
    rintro ⟨z₁, z₂⟩
    obtain ⟨v, h1, h2⟩ := h (0, z₁) (0, z₂)
    refine ⟨(π (v 0), π (v 1), π (v 2)), ?_⟩
    have e1 : c 0 (π (v 0)) - c 1 (π (v 1)) = z₁ := by
      have hh := congrArg Prod.snd h1
      simp only [Prod.snd_sub, hf] at hh
      simpa using hh
    have e2 : c 0 (π (v 0)) - c 2 (π (v 2)) = z₂ := by
      have hh := congrArg Prod.snd h2
      simp only [Prod.snd_sub, hf] at hh
      simpa using hh
    rw [tripleDiffLM2_apply]
    exact Prod.ext e1 e2
  exact tripleDiffLM2_injective_of_surjective (by simp) c hsurj

end Blocks

/-! ## 3. The pair analogue: two blocks, spanning (not injectivity)

The *pair* condition `Work.Drive.PairReg A B` is a **spanning** condition of two class `2`-planes
(`range A ⊔ range B = ⊤`), not an injectivity condition, and it follows from the joint transversality of
the two block maps by the same projection argument — without any dimension count, because the class
projection of a surjective map is surjective. -/

/-- **`PairReg`-shaped conclusion from the joint transversality of two blocks.**  If the second
component of `f k` is `(c k) ∘ π` (`k = 0,1`) and the pair difference map `v ↦ f 0 v.1 - f 1 v.2` is
onto, then the two class `2`-planes span the class tangent space. -/
theorem range_sup_eq_top_of_pairTransverse_blocks
    (π : Tgt3 →L[ℝ] Tgt2)
    (f : Fin 2 → Tgt3 →L[ℝ] ℝ × Tgt3) (c : Fin 2 → Tgt2 →L[ℝ] Tgt3)
    (hf : ∀ k v, (f k v).2 = c k (π v))
    (h : Function.Surjective (fun v : Tgt3 × Tgt3 => f 0 v.1 - f 1 v.2)) :
    (c 0).range ⊔ (c 1).range = ⊤ := by
  have hsurj : ∀ z : Tgt3, ∃ a : Tgt2 × Tgt2, c 0 a.1 - c 1 a.2 = z := by
    intro z
    obtain ⟨v, hv⟩ := h (0, z)
    refine ⟨(π v.1, π v.2), ?_⟩
    have hh := congrArg Prod.snd hv
    simp only [Prod.snd_sub, hf] at hh
    simpa using hh
  rw [Submodule.eq_top_iff']
  intro z
  obtain ⟨a, ha⟩ := hsurj z
  rw [← ha]
  exact sub_mem (Submodule.mem_sup_left (LinearMap.mem_range_self _ _))
    (Submodule.mem_sup_right (LinearMap.mem_range_self _ _))


/-- **The pair analogue with a *mixed* pair of domains** (the shape of a loop-versus-sweep meet: the
loop's derivative has a `2`-dimensional parameter and the sweep's a `3`-dimensional one). -/
theorem range_sup_eq_top_of_pairTransverse_mixed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : E →L[ℝ] Tgt2) (f : E →L[ℝ] ℝ × Tgt3) (c₀ : Tgt2 →L[ℝ] Tgt3)
    (hf : ∀ v : E, (f v).2 = c₀ (φ v))
    (π : Tgt3 →L[ℝ] Tgt2) (g : Tgt3 →L[ℝ] ℝ × Tgt3) (c₁ : Tgt2 →L[ℝ] Tgt3)
    (hg : ∀ v : Tgt3, (g v).2 = c₁ (π v))
    (h : Function.Surjective (fun w : E × Tgt3 => f w.1 - g w.2)) :
    c₀.range ⊔ c₁.range = ⊤ := by
  have hsurj : ∀ z : Tgt3, ∃ a : Tgt2 × Tgt2, c₀ a.1 - c₁ a.2 = z := by
    intro z
    obtain ⟨w, hw⟩ := h (0, z)
    refine ⟨(φ w.1, π w.2), ?_⟩
    have hh := congrArg Prod.snd hw
    simp only [Prod.snd_sub, hf, hg] at hh
    simpa using hh
  rw [Submodule.eq_top_iff']
  intro z
  obtain ⟨a, ha⟩ := hsurj z
  rw [← ha]
  exact sub_mem (Submodule.mem_sup_left (LinearMap.mem_range_self _ _))
    (Submodule.mem_sup_right (LinearMap.mem_range_self _ _))


end

end Work.Drive
