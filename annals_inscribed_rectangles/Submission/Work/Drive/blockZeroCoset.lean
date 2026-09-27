import Mathlib

/-!
# The coset lemma of the ends-clause richness: a `2`-dimensional block-`0` reach suffices

`ENCODED_GENERIC_DEAD.md` (first version, 18:5x) claimed that the parametrised-Sard route to §2.1 is
*dead* because at a zero whose block-`0` chain has `betaG = 0` the image of the parameter derivative of
the charted triple-difference map is confined to a proper subspace.  That claim is **wrong in general**:
it holds only for the families `Work.Drive.encShearFam` / `Work.Drive.encFamTwo` of
`Drive/encodedFamily.lean` / `Drive/encFamTwo.lean`, which do **not** reparametrise the domain of
block `0`.  The lead's family (`NOTES_LEAD_hodd_blockT6.md` §2.2) *does* — it contains the shear
`Sh_{q₀}` of block `0`'s plane coordinates — and then block `0`'s parameter derivative is still
alive at `betaG = 0`, with a **2-dimensional** class reach `W₀`.

This file proves the linear algebra that makes that enough.

Let `A' := spanA ⊆ ℝ³` and `B' := spanB ⊆ ℝ³` be the reaches of the two plane blocks (subspaces of the
class chart) and `W₀ ⊆ ℝ³` the reach of block `0`.  The parameter derivative of the charted
triple-difference map is onto `ℝ⁸ = ℝ⁴ × ℝ⁴` iff the pair map

> `(P, r₁, r₂) ↦ (P - r₁, P - r₂)`,  `P ∈ W₀ ⊕ 0`, `r₁ ∈ A' ⊕ ℝe₃`, `r₂ ∈ B' ⊕ ℝe₃`

is onto, i.e. iff **for every `a b : ℝ³` there is `w ∈ W₀` with `w - a ∈ A'` and `w - b ∈ B'`**
(the level coordinates are free, because the twists `r₁`, `r₂` supply `ℝ e₃`).

`exists_mem_inter_cosets_of_sup_eq_top` shows that this holds as soon as

* `A' ⊔ B' = ⊤` (`PairReg`, i.e. `Work.Drive.PairReg` at the meet — the design's hypothesis), **and**
* `W₀ ⊔ (A' ⊓ B') = ⊤` (a condition on the geometry of the three plane presentations at the meet:
  the line `A' ⊓ B'` is not contained in the `2`-plane `W₀`; generically true).

In particular **a `2`-dimensional `W₀` suffices** — no `3`-dimensional block-`0` class reach is needed,
contrary to §1/§3 of the first version of `ENCODED_GENERIC_DEAD.md`. -/

namespace Work.Drive

/-- **The coset lemma**: if two subspaces `A`, `B` span the whole space and a subspace `W₀` together
with `A ⊓ B` spans it as well, then `W₀` meets every coset intersection `(a + A) ∩ (b + B)`. -/
theorem exists_mem_inter_cosets_of_sup_eq_top
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (W₀ A B : Submodule ℝ E) (hA : A ⊔ B = ⊤) (hW : W₀ ⊔ (A ⊓ B) = ⊤)
    (a b : E) :
    ∃ w ∈ W₀, w - a ∈ A ∧ w - b ∈ B := by
  have hab : a - b ∈ A ⊔ B := by rw [hA]; exact Submodule.mem_top
  obtain ⟨α, hαA, β, hβB, hαβ⟩ := Submodule.mem_sup.mp hab
  have hx₀a : (a - α) - a ∈ A := by simpa using neg_mem hαA
  have hx₀b : (a - α) - b ∈ B := by
    have h1 : (a - α) - b = (a - b) - α := by abel
    rw [h1, ← hαβ]
    simpa using hβB
  have hx₀ : a - α ∈ W₀ ⊔ (A ⊓ B) := by rw [hW]; exact Submodule.mem_top
  obtain ⟨w, hwW, d, hd, hwd⟩ := Submodule.mem_sup.mp hx₀
  obtain ⟨hdA, hdB⟩ := hd
  refine ⟨w, hwW, ?_, ?_⟩
  · have h1 : w - a = ((a - α) - a) - d := by rw [← hwd]; abel
    rw [h1]; exact sub_mem hx₀a hdA
  · have h1 : w - b = ((a - α) - b) - d := by rw [← hwd]; abel
    rw [h1]; exact sub_mem hx₀b hdB

end Work.Drive
