import Mathlib
import Submission.Work.EKLC6Core.cellsData_atom_facts
import Submission.Work.EKLC6Core.cellW_margin
import Submission.Work.EKLC6Core.margin_le_cellDeltaW
import Submission.Work.EKLC6Core.liftW_smul_eq
import Submission.Work.EKLC6Core.genCW_mem_iff

namespace Work.EKLC6Core

theorem margin_mem_atom_pointwise {μ : MeasureTheory.Measure Work.EKLContract.X3}
    {U : Subgroup Work.EKLContract.SL3}
    {Q : ℕ → Set Work.EKLContract.X3} {d : ℕ → ℝ} {g : ℕ → Work.EKLContract.SL3}
    {O : ℕ → Set Work.EKLContract.SL3}
    (hopen : ∀ k, IsOpen (Q k)) (hdisj : ∀ k l, k ≠ l → Disjoint (Q k) (Q l))
    (hcover : μ (Set.iUnion fun k => Q k)ᶜ = 0)
    (hdpos : ∀ k, 0 < d k) (hdsmall : ∀ k, d k ≤ 1 / 16)
    (hsub : ∀ k, Q k ⊆ (fun v : Work.EKLContract.SL3 => v • Work.EKLContract.mkX (g k)) ''
      (Work.EKLContract.V (d k / 2)))
    (hinj : ∀ k (v₁ v₂ : Work.EKLContract.SL3), v₁ ∈ Work.EKLContract.V (4 * d k) →
      v₂ ∈ Work.EKLContract.V (4 * d k) →
      v₁ • Work.EKLContract.mkX (g k) = v₂ • Work.EKLContract.mkX (g k) → v₁ = v₂)
    (hOopen : ∀ m, IsOpen (O m))
    (hOsep : ∀ z w : Work.EKLContract.SL3,
      (∀ m, (z ∈ Work.EKLC6Core.satUC U (O m) ↔ w ∈ Work.EKLC6Core.satUC U (O m))) →
      w ∈ Work.EKLC6Core.satUC U ({z} : Set Work.EKLContract.SL3))
    {k n : ℕ} {y : Work.EKLContract.X3} (hy : y ∈ Q k)
    {c lam : ℝ} (hc : 0 < c) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hdepth : ∀ v : Work.EKLContract.SL3, v ∈ Work.EKLContract.V (c * lam ^ n) →
      v • y ∈ Q k)
    {u : Work.EKLContract.SL3} (huU : u ∈ U)
    (huV : u ∈ Work.EKLContract.V (c * lam ^ n)) :
    u • y ∈ Work.EKLContract.atom (Work.EKLC6Core.MSigCut U Q d g O) y := by
  classical
  -- The `μ`-free residue of the hypotheses is a `CellW`: the cell family together with its
  -- scales, centres, containment in the lifted half-ball and injectivity on the lifted ball.
  let S : CellW μ U :=
    { Q := Q, hopen := hopen, hdisj := hdisj, hcover := hcover, δ := d,
      hδpos := hdpos, hδsmall := hdsmall, g := g, hsub := hsub, hinj := hinj }
  -- The margin hypothesis puts `u • y` into the same cell as `y`.
  have hyu : u • y ∈ Q k := hdepth u huV
  -- Uncrossedness at scale `c * lam ^ n` forces that scale below twice the cell radius.
  have hε : c * lam ^ n ≤ 2 * d k :=
    margin_le_cellDeltaW S hy (ε := c * lam ^ n) (fun v hv => hdepth v hv)
  -- Hence the canonical lift is equivariant under the small `U`-element `u`.
  have hlift : liftW S k (u • y) = u * liftW S k y :=
    liftW_smul_eq S hy huV hε hyu
  -- It remains to compare the membership patterns of `y` and `u • y` in the generators.
  rw [MSigCut, mem_atom_generateFrom_iff]
  intro A hA
  rcases hA with ⟨k', rfl⟩ | ⟨⟨k', m⟩, rfl⟩
  · -- the cell `Q k'` cannot separate two points of the same cell
    by_cases hkk : k' = k
    · rw [hkk]; exact ⟨fun _ => hy, fun _ => hyu⟩
    · exact iff_of_false (fun hc => Set.disjoint_left.mp (hdisj k' k hkk) hc hyu)
        (fun hc => Set.disjoint_left.mp (hdisj k' k hkk) hc hy)
  · -- the clipped cylinder generator: for `k' = k` the canonical lifts decide membership,
    -- and `satU U (O m)` is invariant under left multiplication by `u ∈ U`
    by_cases hkk : k' = k
    · rw [hkk]
      change u • y ∈ genCut U Q d g O k m ↔ y ∈ genCut U Q d g O k m
      rw [show genCut U Q d g O k m = genCW S O k m from rfl]
      rw [genCW_mem_iff S O k m hyu, genCW_mem_iff S O k m hy, hlift,
        mem_satU_mul_iffW huU (O m) (liftW S k y)]
    · exact iff_of_false (fun hc => Set.disjoint_left.mp (hdisj k' k hkk) hc.2 hyu)
        (fun hc => Set.disjoint_left.mp (hdisj k' k hkk) hc.2 hy)

end Work.EKLC6Core
