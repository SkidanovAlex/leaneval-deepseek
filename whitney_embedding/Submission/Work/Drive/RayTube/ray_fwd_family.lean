import Mathlib
import Submission.Work.Drive.RayTube.RaySetup

/-!
# The forward family of pieces along a ray

Port of the forward recursion `ctcFwd`/`ctc_fwd_family`
(`Submission/Work/Noncompact/CompressionTube/ctc/final.lean`) to the ray `RayData`:

from raw pieces `ψ m` transverse on the parameter window `[m - 2, m + 2]` we build a family `Ψ m`
of pieces, each vanishing on the ray, with

* `Ψ m` transverse on `(m - 13/8, m + 2)`,
* `Ψ (m+1) = Ψ m` on the region `{g ≤ m + 1 - 1/8}`,

so that the function `x ↦ Ψ ⌊g x + 1/4⌋ x` is smooth and transverse along the ray.  The recursion
step is `ray_step` (the ray version of `ctc_step_exists`).
-/

namespace Work.Drive.RayTube

open scoped Manifold ContDiff
open Topology Set Function
open Work.Noncompact.CompressionTube

noncomputable section

/-- The state of the forward recursion at level `m`. -/
structure RayFwdState {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    (D : RayData n M) (m : ℕ) where
  prev : M → EuclideanSpace ℝ (Fin (n - 1))
  cur : M → EuclideanSpace ℝ (Fin (n - 1))
  hc : ContMDiff (MC n) (MC (n - 1)) smoothOrder cur
  h0 : ∀ s : ℝ, 0 ≤ s → cur (D.ρ s) = 0
  hT : ∀ s : ℝ, 0 ≤ s → s ∈ Set.Ioo ((m : ℝ) - 13 / 8) ((m : ℝ) + 2) →
    Transverse D.ρ D.g cur s
  heq : ∀ x : M, D.g x ≤ (m : ℝ) - 1 / 8 → cur x = prev x

set_option maxHeartbeats 1600000 in
/-- The forward recursion along the ray. -/
noncomputable def rayFwd {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M] (D : RayData n M)
    {ψ : ℕ → M → EuclideanSpace ℝ (Fin (n - 1))}
    (hψc : ∀ m : ℕ, ContMDiff (MC n) (MC (n - 1)) smoothOrder (ψ m))
    (hψ0 : ∀ (m : ℕ) (s : ℝ), 0 ≤ s → ψ m (D.ρ s) = 0)
    (hψT : ∀ (m : ℕ) (s : ℝ), 0 ≤ s → s ∈ Set.Icc ((m : ℝ) - 2) ((m : ℝ) + 2) →
      Transverse D.ρ D.g (ψ m) s) :
    (m : ℕ) → RayFwdState (n := n) D m
  | 0 =>
      { prev := ψ 0
        cur := ψ 0
        hc := hψc 0
        h0 := fun s hs => hψ0 0 s hs
        hT := fun s hs hsI => hψT 0 s hs (by
          rw [Set.mem_Ioo] at hsI
          rw [Set.mem_Icc]
          exact ⟨by push_cast at hsI ⊢; linarith, by push_cast at hsI ⊢; linarith⟩)
        heq := fun x _ => rfl }
  | (m + 1) => by
      classical
      set st := rayFwd hn D hψc hψ0 hψT m with hst
      have hwin : ∀ s : ℝ, 0 ≤ s → s ∈ Set.Ioo (((m + 1 : ℕ) : ℝ) - 21 / 8)
          (((m + 1 : ℕ) : ℝ) + 1) → Transverse D.ρ D.g st.cur s := by
        intro s hs0 hs
        refine st.hT s hs0 ?_
        refine Set.mem_Ioo.mpr ⟨?_, ?_⟩
        · have h := hs.1; push_cast at h ⊢; linarith
        · have h := hs.2; push_cast at h ⊢; linarith
      have hraw : ∀ s : ℝ, 0 ≤ s → s ∈ Set.Icc (((m + 1 : ℕ) : ℝ) - 2)
          (((m + 1 : ℕ) : ℝ) + 2) → Transverse D.ρ D.g (ψ (m + 1)) s := by
        intro s hs0 hs
        refine hψT (m + 1) s hs0 (Set.mem_Icc.mpr ⟨?_, ?_⟩)
        · have h := hs.1; push_cast at h ⊢; linarith
        · have h := hs.2; push_cast at h ⊢; linarith
      let hex := ray_step hn D (k := ((m + 1 : ℕ) : ℤ)) (by omega) st.hc (hψc (m + 1)) st.h0
        (hψ0 (m + 1)) hwin hraw
      let Ψ' : M → EuclideanSpace ℝ (Fin (n - 1)) := Classical.choose hex
      let d : ℝ := Classical.choose (Classical.choose_spec hex)
      have hspec : 0 < d ∧ d ≤ 1 / 8 ∧
          ContMDiff (MC n) (MC (n - 1)) smoothOrder Ψ' ∧
          (∀ s : ℝ, 0 ≤ s → Ψ' (D.ρ s) = 0) ∧
          (∀ s : ℝ, 0 ≤ s → s ∈ Set.Ioo ((((m + 1 : ℕ) : ℤ) : ℝ) - 13 / 8)
              ((((m + 1 : ℕ) : ℤ) : ℝ) + 2) → Transverse D.ρ D.g Ψ' s) ∧
          (∀ x : M, D.g x ≤ ((((m + 1 : ℕ) : ℤ) : ℝ)) - d → Ψ' x = st.cur x) :=
        Classical.choose_spec (Classical.choose_spec hex)
      refine ⟨st.cur, Ψ', hspec.2.2.1, hspec.2.2.2.1, ?_, ?_⟩
      · intro s hs0 hs
        refine hspec.2.2.2.2.1 s hs0 ?_
        refine Set.mem_Ioo.mpr ⟨?_, ?_⟩
        · have h := hs.1; push_cast at h ⊢; linarith
        · have h := hs.2; push_cast at h ⊢; linarith
      · intro x hx
        refine hspec.2.2.2.2.2 x ?_
        have h := hx; push_cast at h ⊢
        linarith [hspec.1, hspec.2.1]

set_option backward.isDefEq.respectTransparency false in
/-- **The forward family along a ray.** -/
theorem ray_fwd_family {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M] (D : RayData n M)
    {ψ : ℕ → M → EuclideanSpace ℝ (Fin (n - 1))}
    (hψc : ∀ m : ℕ, ContMDiff (MC n) (MC (n - 1)) smoothOrder (ψ m))
    (hψ0 : ∀ (m : ℕ) (s : ℝ), 0 ≤ s → ψ m (D.ρ s) = 0)
    (hψT : ∀ (m : ℕ) (s : ℝ), 0 ≤ s → s ∈ Set.Icc ((m : ℝ) - 2) ((m : ℝ) + 2) →
      Transverse D.ρ D.g (ψ m) s) :
    ∃ Ψ : ℕ → M → EuclideanSpace ℝ (Fin (n - 1)),
      (∀ m : ℕ, ContMDiff (MC n) (MC (n - 1)) smoothOrder (Ψ m)) ∧
      (∀ (m : ℕ) (s : ℝ), 0 ≤ s → Ψ m (D.ρ s) = 0) ∧
      (∀ (m : ℕ) (s : ℝ), 0 ≤ s → s ∈ Set.Ioo ((m : ℝ) - 13 / 8) ((m : ℝ) + 2) →
        Transverse D.ρ D.g (Ψ m) s) ∧
      (∀ (m : ℕ) (x : M), D.g x ≤ ((m : ℝ) + 1) - 1 / 8 → Ψ (m + 1) x = Ψ m x) ∧
      Ψ 0 = ψ 0 := by
  classical
  refine ⟨fun m => (rayFwd hn D hψc hψ0 hψT m).cur, fun m => (rayFwd hn D hψc hψ0 hψT m).hc,
    fun m s hs => (rayFwd hn D hψc hψ0 hψT m).h0 s hs,
    fun m s hs hsI => (rayFwd hn D hψc hψ0 hψT m).hT s hs hsI, ?_, ?_⟩
  · intro m x hx
    have hx' : D.g x ≤ ((m + 1 : ℕ) : ℝ) - 1 / 8 := by push_cast at hx ⊢; linarith
    have h1 := (rayFwd hn D hψc hψ0 hψT (m + 1)).heq x hx'
    have h2 : (rayFwd hn D hψc hψ0 hψT (m + 1)).prev x
        = (rayFwd hn D hψc hψ0 hψT m).cur x := by simp only [rayFwd]
    show (rayFwd hn D hψc hψ0 hψT (m + 1)).cur x = (rayFwd hn D hψc hψ0 hψT m).cur x
    exact h1.trans h2
  · simp only [rayFwd]

end

end Work.Drive.RayTube
