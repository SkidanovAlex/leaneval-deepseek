import Mathlib
import Submission.Work.EKLC6Core.PlaqueCellDefs
import Submission.Work.EKLC6Core.CellBaseCore
import Submission.Work.EKLC6Core.atom_MSig2
import Submission.Work.EKLC6Core.cell_facts_of_base
import Submission.Work.EKLC6Core.V_estimates
import Submission.Work.EKLComp.LeafDefs

/-!
# `Work.EKLC6Core.shape_uball_base`

The shape of an `MSig2`-atom at a free point of a cell of a raw cell family is contained in a
fixed `U`-ball of `SL₃(ℝ)`: the `CellBase` analogue of the `CellSys` statement
`Work.EKLC6Core.shape_MSig_uball`.

The proof is the proof of `shape_MSig_uball` transported along the `CellSys → CellBase`
transport: the shape of the `MSig2`-atom at `y ∈ S.Q k` is

`{u ∈ U | u * lift2 S k y ∈ lifted (δ k) (g k) ∧ u • y ∈ S.Q k}`

(`shape_MSig2`, whose measurability hypothesis is *not used*: the atom identity of `CellBaseCore`
holds for the raw family without any measurability of the clipped generators, because the
pattern-class description of the atom of a generated σ-algebra is a purely pointwise statement).
If `u ∈ U` and both `lift2 S k y` and `u * lift2 S k y` lie in the same lifted ball
`V (δ k) · g k`, then writing `u * lift2 S k y = v₁ * g k`, `lift2 S k y = v₂ * g k` with
`v₁, v₂ ∈ V (δ k)` and cancelling `g k` on the right gives `u = v₁ * v₂⁻¹`, which lies in
`V (14 δ k)` by `V_estimates`; since `δ k ≤ 1/16`, this is inside `Uball U 1`.

For this we only need the two atom/shape identities *without* the (unused) measurability
hypothesis; those are recorded here as `atom_MSig2'` and `shape_MSig2'` (the proofs are literally
the proofs of `atom_MSig2`/`shape_MSig2`, the hypothesis `hmeas` never entering the argument).
-/

namespace Work.EKLC6Core

open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {μ : MeasureTheory.Measure X3} {U : Subgroup SL3}

/-! ## The atom identity without the measurability hypothesis -/

/-- **The atoms of `MSig2` inside a cell are the `U`-orbit pieces cut by the lifted ball.**
(The proof of `atom_MSig2` does not use its measurability hypothesis, so it is dropped here.) -/
theorem atom_MSig2' (S : CellBase μ U) (O : ℕ → Set SL3)
    (hOsep : ∀ g g' : SL3,
      (∀ m, (∃ u ∈ U, u * g ∈ O m) ↔ (∃ u ∈ U, u * g' ∈ O m)) → ∃ u ∈ U, g' = u * g)
    {k : ℕ} {y : X3} (hy : y ∈ S.Q k) :
    atom (MSig2 U S.Q S.δ S.g O) y
      = mkX '' ({g : SL3 | ∃ u ∈ U, g = u * lift2 S k y}
        ∩ lifted (S.δ k) (S.g k)) ∩ S.Q k := by
  classical
  have key : ∀ z : X3, z ∈ atom (MSig2 U S.Q S.δ S.g O) y ↔
      ∀ s ∈ fam2 U S.Q S.δ S.g O, (z ∈ s ↔ y ∈ s) := by
    intro z
    have h : MSig2 U S.Q S.δ S.g O = MeasurableSpace.generateFrom (fam2 U S.Q S.δ S.g O) :=
      MSig2_eq_generateFrom_fam2 U S.Q S.δ S.g O
    rw [h]
    exact atomMSig_mem_atom_generateFrom
  ext z
  constructor
  · -- every point of the atom lies in the piece of the `U`-orbit of the lift of `y`
    intro hz
    have hp : ∀ s ∈ fam2 U S.Q S.δ S.g O, (z ∈ s ↔ y ∈ s) := (key z).mp hz
    have hzQ : z ∈ S.Q k := (hp (S.Q k) (Or.inl ⟨k, rfl⟩)).mpr hy
    have hgen : ∀ m, z ∈ genC2 U S.Q S.δ S.g O k m ↔ y ∈ genC2 U S.Q S.δ S.g O k m :=
      fun m => hp (genC2 U S.Q S.δ S.g O k m) (Or.inr ⟨(k, m), rfl⟩)
    have hsat : ∀ m, lift2 S k z ∈ satU U (O m) ↔ lift2 S k y ∈ satU U (O m) :=
      fun m => ((mem_genC2_iff S O hzQ).symm.trans (hgen m)).trans (mem_genC2_iff S O hy)
    have hsat' : ∀ m, (∃ u ∈ U, u * lift2 S k z ∈ O m) ↔ (∃ u ∈ U, u * lift2 S k y ∈ O m) :=
      fun m => ((atomMSig_mem_satU_iff (U := U) (O m) (lift2 S k z)).symm.trans (hsat m)).trans
        (atomMSig_mem_satU_iff (U := U) (O m) (lift2 S k y))
    obtain ⟨u, huU, huy⟩ := hOsep (lift2 S k z) (lift2 S k y) hsat'
    have hwit : lift2 S k z = u⁻¹ * lift2 S k y := by rw [huy, inv_mul_cancel_left]
    exact ⟨⟨lift2 S k z, ⟨⟨u⁻¹, U.inv_mem huU, hwit⟩, lift2_mem S k hzQ⟩,
      mkX_lift2 S k hzQ⟩, hzQ⟩
  · -- and conversely every point of that piece has the same pattern as `y`
    intro hz
    obtain ⟨⟨w, ⟨hwW, hwl⟩, hwz⟩, hzQ⟩ := hz
    obtain ⟨u, huU, hwu⟩ := hwW
    have hℓw : lift2 S k z = w :=
      mkX_inj_lifted2 S k (lift2_mem S k hzQ) hwl
        (by rw [mkX_lift2 S k hzQ, hwz])
    have hℓ : lift2 S k z = u * lift2 S k y := by rw [hℓw, hwu]
    refine (key z).mpr fun s hs => ?_
    rcases hs with ⟨j, hj⟩ | ⟨⟨i, m⟩, him⟩
    · rw [← hj]
      by_cases hjk : j = k
      · rw [hjk]; exact ⟨fun _ => hy, fun _ => hzQ⟩
      · exact iff_of_false (Set.disjoint_left.mp (S.hdisj k j (Ne.symm hjk)) hzQ)
          (Set.disjoint_left.mp (S.hdisj k j (Ne.symm hjk)) hy)
    · rw [← him]
      by_cases hik : i = k
      · rw [hik, mem_genC2_iff S O hzQ, mem_genC2_iff S O hy, hℓ,
          atomMSig_satU_mul_iff (U := U) (O m) huU]
      · exact iff_of_false
          (fun h => Set.disjoint_left.mp (S.hdisj i k hik) h.2 hzQ)
          (fun h => Set.disjoint_left.mp (S.hdisj i k hik) h.2 hy)

/-! ## The shape of an `MSig2`-atom, without the measurability hypothesis -/

/-- **The shape of an atom of `MSig2`** (without the unused measurability hypothesis). -/
theorem shape_MSig2' (S : CellBase μ U) (O : ℕ → Set SL3)
    (hOsep : ∀ g g' : SL3,
      (∀ m, (∃ u ∈ U, u * g ∈ O m) ↔ (∃ u ∈ U, u * g' ∈ O m)) → ∃ u ∈ U, g' = u * g)
    {k : ℕ} {y : X3} (hy : y ∈ S.Q k) (hfree : ∀ u ∈ U, u • y = y → u = 1) :
    shape (MSig2 U S.Q S.δ S.g O) U y
      = {u : SL3 | u ∈ U ∧ u * lift2 S k y ∈ lifted (S.δ k) (S.g k) ∧ u • y ∈ S.Q k} := by
  have hatom := atom_MSig2' S O hOsep hy
  have hℓmk : mkX (lift2 S k y) = y := mkX_lift2 S k hy
  ext u
  constructor
  · rintro ⟨huU, huA⟩
    rw [hatom] at huA
    obtain ⟨huA', huyQ⟩ := huA
    obtain ⟨g, hgmem, hgk⟩ := huA'
    obtain ⟨hgcos, hgl⟩ := hgmem
    obtain ⟨u₀, hu₀U, hgu⟩ := hgcos
    have hgl' : u₀ * lift2 S k y ∈ lifted (S.δ k) (S.g k) := by rw [← hgu]; exact hgl
    have huy : u • y = u₀ • y := by
      rw [← hgk, hgu, ← smul_mkX_eq u₀ (lift2 S k y), hℓmk]
    have hfix : (u₀⁻¹ * u) • y = y := by rw [mul_smul, huy, inv_smul_smul]
    have hu_eq : u = u₀ := by
      have h1 : u₀⁻¹ * u = 1 := hfree _ (U.mul_mem (U.inv_mem hu₀U) huU) hfix
      calc u = u₀ * (u₀⁻¹ * u) := (mul_inv_cancel_left u₀ u).symm
        _ = u₀ * 1 := by rw [h1]
        _ = u₀ := mul_one u₀
    refine ⟨huU, ?_, huyQ⟩
    rw [hu_eq]
    exact hgl'
  · rintro ⟨huU, hgl, huyQ⟩
    refine ⟨huU, ?_⟩
    rw [hatom]
    refine ⟨⟨u * lift2 S k y, ⟨⟨u, huU, rfl⟩, hgl⟩, ?_⟩, huyQ⟩
    rw [← smul_mkX_eq u (lift2 S k y), hℓmk]

/-! ## The target: the shape is contained in a fixed `U`-ball -/

theorem shape_uball_base {μ : MeasureTheory.Measure Work.EKLContract.X3}
    {U : Subgroup Work.EKLContract.SL3} (S : Work.EKLC6Core.CellBase μ U)
    (O : ℕ → Set Work.EKLContract.SL3)
    (hOsep : ∀ g g' : Work.EKLContract.SL3,
      (∀ m, (∃ u ∈ U, u * g ∈ O m) ↔ (∃ u ∈ U, u * g' ∈ O m)) → ∃ u ∈ U, g' = u * g) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (k : ℕ) (y : Work.EKLContract.X3), y ∈ S.Q k →
      (∀ u ∈ U, u • y = y → u = 1) →
      Work.EKLContract.shape (Work.EKLC6Core.MSig2 U S.Q S.δ S.g O) U y ⊆
        Work.EKLComp.Uball U ρ := by
  refine ⟨1, one_pos, ?_⟩
  intro k y hy hfree u hu
  rw [shape_MSig2' S O hOsep hy hfree] at hu
  obtain ⟨huU, hgl, -⟩ := hu
  obtain ⟨v₁, hv₁, hv₁eq⟩ := hgl
  obtain ⟨v₂, hv₂, hv₂eq⟩ := lift2_mem S k hy
  have h1 : v₁ * S.g k = u * lift2 S k y := hv₁eq
  have h2 : v₂ * S.g k = lift2 S k y := hv₂eq
  have h3 : (u * v₂) * S.g k = u * lift2 S k y := by rw [mul_assoc, h2]
  have hcancel : v₁ = u * v₂ := mul_right_cancel (h1.trans h3.symm)
  have hueq : u = v₁ * v₂⁻¹ := eq_mul_inv_iff_mul_eq.mpr hcancel.symm
  have hs : 0 < S.δ k := S.hδpos k
  have hs10 : S.δ k ≤ 1 / 10 := by linarith [S.hδsmall k]
  have hV : u ∈ V (14 * S.δ k) := by
    rw [hueq]
    exact (V_estimates hs hs10).2.1 v₁ v₂ hv₁ hv₂
  refine ⟨huU, fun i j => ?_⟩
  have hlt : 14 * S.δ k < 1 := by linarith [S.hδsmall k]
  exact lt_trans (hV i j) hlt

end Work.EKLC6Core
