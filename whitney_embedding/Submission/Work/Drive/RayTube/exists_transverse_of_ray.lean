import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.collar_defs
import Submission.Work.Drive.RayTube.RaySetup
import Submission.Work.Drive.RayTube.ray_transverse_on_Icc
import Submission.Work.Drive.RayTube.ray_fwd_family
import Submission.Work.Compat.MFDerivCongrV433

/-!
# A transverse coordinate along a smooth proper embedded ray

Given a smooth curve `ρ : ℝ → M` which is injective, proper and an immersion on `[0,∞)`, and a
smooth `g : M → ℝ` with `g (ρ t) = t` for `t ≥ 0`, we produce a smooth `P : M → ℝ^{n-1}` vanishing
on the whole ray and transverse to `g` at every point `ρ t`, `t ≥ 0`.

This is the ray version of `Work.Noncompact.CompressionTube.exists_global_transverse_coordinate`
(`ctc/final.lean`); the chapter is ported to the half-line in `RaySetup.lean`,
`ray_transverse_on_Icc.lean` and `ray_fwd_family.lean`.

The assembled function is `P x = Ψ (⌊g x + 1/4⌋).toNat x`, where `Ψ m` is the forward family of
`ray_fwd_family`: at `ρ s` the index is `⌊s + 1/4⌋`, and `Ψ m` is transverse on the parameter
window `(m - 13/8, m + 2) ∋ s`.
-/

namespace Work.Drive.RayTube

open scoped Manifold ContDiff
open Topology Set Function
open Work.Noncompact.CompressionTube

noncomputable section

open scoped Manifold ContDiff in
open Work.Noncompact.CompressionTube in
theorem exists_transverse_of_ray {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {ρ : ℝ → M} (hρ : ContMDiff MCreal (MC n) smoothOrder ρ)
    (hinj : Set.InjOn ρ (Set.Ici (0:ℝ)))
    (hprop : IsProperMap (fun t : Set.Ici (0:ℝ) => ρ t))
    (himm : ∀ t : ℝ, 0 ≤ t → Function.Injective (mfderiv MCreal (MC n) ρ t))
    {g : M → ℝ} (hg : ContMDiff (MC n) MCreal smoothOrder g)
    (hgc : ∀ t : ℝ, 0 ≤ t → g (ρ t) = t) :
    ∃ P : M → EuclideanSpace ℝ (Fin (n - 1)), ContMDiff (MC n) (MC (n - 1)) smoothOrder P ∧
      (∀ t : ℝ, 0 ≤ t → P (ρ t) = 0) ∧
      (∀ t : ℝ, 0 ≤ t → Transverse ρ g P t) := by
  classical
  let D : RayData n M := ⟨ρ, hρ, hinj, hprop, himm, g, hg, hgc⟩
  -- (1) the raw pieces, one for every integer window `[m-2, m+2]`
  have hraw : ∀ m : ℕ, ∃ ψ : M → EuclideanSpace ℝ (Fin (n - 1)),
      ContMDiff (MC n) (MC (n - 1)) smoothOrder ψ ∧
      (∀ s : ℝ, 0 ≤ s → ψ (ρ s) = 0) ∧
      ∀ s : ℝ, 0 ≤ s → s ∈ Set.Icc ((m : ℝ) - 2) ((m : ℝ) + 2) →
        Transverse ρ g ψ s := by
    intro m
    obtain ⟨Ψm, hc, h0, hT⟩ :=
      ray_transverse_on_Icc hn D (a := max 0 ((m : ℝ) - 2)) (b := (m : ℝ) + 2)
        (le_max_left _ _) (max_le (by positivity) (by linarith))
    exact ⟨Ψm, hc, h0, fun s hs0 hs =>
      hT s hs0 ⟨max_le hs0 hs.1, hs.2⟩⟩
  choose ψ hψc hψ0 hψT using hraw
  -- (2) the forward family
  obtain ⟨Ψ, hΨc, hΨ0, hΨT, hΨeq, hΨ0eq⟩ := ray_fwd_family hn D hψc hψ0 hψT
  -- (3) the assembly: the index used at `x` is `(⌊g x + 1/4⌋).toNat`
  have hloc : ∀ x₀ : M, (fun x : M => Ψ (Int.toNat ⌊g x + 1 / 4⌋) x)
      =ᶠ[𝓝 x₀] Ψ (Int.toNat ⌊g x₀ + 1 / 4⌋) := by
    intro x₀
    set k : ℤ := ⌊g x₀ + 1 / 4⌋ with hk
    have hk1 : (k : ℝ) ≤ g x₀ + 1 / 4 := by rw [hk]; exact Int.floor_le _
    have hk2 : g x₀ + 1 / 4 < (k : ℝ) + 1 := by rw [hk]; exact Int.lt_floor_add_one _
    rcases lt_or_eq_of_le hk1 with hlt | heq
    · -- the floor is locally constant `k`
      have hopen : IsOpen {y : M | (k : ℝ) - 1 / 4 < g y ∧ g y < (k : ℝ) + 3 / 4} :=
        (isOpen_lt continuous_const hg.continuous).inter
          (isOpen_lt hg.continuous continuous_const)
      have hmem : x₀ ∈ {y : M | (k : ℝ) - 1 / 4 < g y ∧ g y < (k : ℝ) + 3 / 4} :=
        ⟨by linarith, by linarith⟩
      filter_upwards [hopen.mem_nhds hmem] with y hy
      have hfloor : ⌊g y + 1 / 4⌋ = k := by
        rw [Int.floor_eq_iff]
        exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
      rw [hfloor]
    · -- the index meets the jump `g x₀ = k - 1/4`; the two pieces agree there
      have hge : g x₀ = (k : ℝ) - 1 / 4 := by linarith
      have hnhds : {y : M | |g y + 1 / 4 - (k : ℝ)| < 1 / 2} ∈ 𝓝 x₀ := by
        have h0 : |g x₀ + 1 / 4 - (k : ℝ)| < 1 / 2 := by rw [hge]; norm_num
        exact (isOpen_lt ((hg.continuous.add continuous_const).sub continuous_const).abs
          continuous_const).mem_nhds h0
      have hgear : Ψ (Int.toNat k) =ᶠ[𝓝 x₀] Ψ (Int.toNat (k - 1)) := by
        by_cases hk0 : (1 : ℤ) ≤ k
        · have hsucc : (k - 1).toNat + 1 = k.toNat := by
            have h1 : (((k - 1).toNat : ℕ) : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
            have h2 : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg (by omega)
            omega
          have hmR : (((k - 1).toNat : ℕ) : ℝ) = (k : ℝ) - 1 := by
            have h1 : (((k - 1).toNat : ℕ) : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
            have h2 := congrArg (fun z : ℤ => (z : ℝ)) h1
            push_cast at h2 ⊢
            linarith
          have hle : g x₀ < (((k - 1).toNat : ℕ) : ℝ) + 1 - 1 / 8 := by
            rw [hmR]; linarith
          filter_upwards [(isOpen_lt hg.continuous continuous_const).mem_nhds hle] with y hy
          have h := hΨeq (k - 1).toNat y (le_of_lt hy)
          rwa [hsucc] at h
        · rw [Int.toNat_of_nonpos (by omega : k ≤ 0),
              Int.toNat_of_nonpos (by omega : k - 1 ≤ 0)]
      filter_upwards [hnhds, hgear] with y hy hgy
      have hy1 : (k : ℝ) - 1 / 2 < g y + 1 / 4 := by
        have h := abs_lt.mp hy; linarith [h.1]
      have hy2 : g y + 1 / 4 < (k : ℝ) + 1 / 2 := by
        have h := abs_lt.mp hy; linarith [h.2]
      have hup : ⌊g y + 1 / 4⌋ ≤ k := by
        rw [Int.floor_le_iff]; linarith
      have hlow : k - 1 ≤ ⌊g y + 1 / 4⌋ := by
        rw [Int.le_floor]; push_cast; linarith
      have hfloor : ⌊g y + 1 / 4⌋ = k ∨ ⌊g y + 1 / 4⌋ = k - 1 := by omega
      rcases hfloor with hf | hf
      · rw [hf]
      · rw [hf]
        exact hgy.symm
  -- smoothness
  have hPsm : ContMDiff (MC n) (MC (n - 1)) smoothOrder
      (fun x : M => Ψ (Int.toNat ⌊g x + 1 / 4⌋) x) := by
    intro x₀
    exact ((hΨc (Int.toNat ⌊g x₀ + 1 / 4⌋)).contMDiffAt).congr_of_eventuallyEq (hloc x₀)
  -- vanishing on the ray
  have hP0 : ∀ s : ℝ, 0 ≤ s → (fun x : M => Ψ (Int.toNat ⌊g x + 1 / 4⌋) x) (ρ s) = 0 := by
    intro s hs
    have hone : ⌊g (ρ s) + 1 / 4⌋ = ⌊s + 1 / 4⌋ := by rw [hgc s hs]
    simp only
    rw [hone]
    exact hΨ0 (Int.toNat ⌊s + 1 / 4⌋) s hs
  -- transversality
  have hPtr : ∀ s : ℝ, 0 ≤ s → Transverse ρ g
      (fun x : M => Ψ (Int.toNat ⌊g x + 1 / 4⌋) x) s := by
    intro s hs
    intro v h1 h2
    have hk0 : (0 : ℤ) ≤ ⌊s + 1 / 4⌋ := by
      rw [Int.le_floor]; push_cast; linarith
    have hm : (((Int.toNat ⌊s + 1 / 4⌋ : ℕ)) : ℝ) = (⌊s + 1 / 4⌋ : ℝ) := by
      have h1' : ((Int.toNat ⌊s + 1 / 4⌋ : ℕ) : ℤ) = ⌊s + 1 / 4⌋ := Int.toNat_of_nonneg hk0
      have := congrArg (fun z : ℤ => (z : ℝ)) h1'
      push_cast at this ⊢
      exact this
    have hder : mfderiv (MC n) (MC (n - 1))
        (fun x : M => Ψ (Int.toNat ⌊g x + 1 / 4⌋) x) (ρ s)
        = mfderiv (MC n) (MC (n - 1)) (Ψ (Int.toNat ⌊s + 1 / 4⌋)) (ρ s) := by
      have h := Filter.EventuallyEq.mfderiv_eq_v433 (I := MC n) (I' := MC (n - 1)) (hloc (ρ s))
      rwa [show ⌊g (ρ s) + 1 / 4⌋ = ⌊s + 1 / 4⌋ from by rw [hgc s hs]] at h
    have hfl1 : ((⌊s + 1 / 4⌋ : ℤ) : ℝ) ≤ s + 1 / 4 := Int.floor_le _
    have hfl2 : s + 1 / 4 < ((⌊s + 1 / 4⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have hgt : mfderiv (MC n) (MC (n - 1)) (Ψ (Int.toNat ⌊s + 1 / 4⌋)) (ρ s) v = 0 := by
      rw [← hder]
      exact h1
    refine hΨT (Int.toNat ⌊s + 1 / 4⌋) s hs (Set.mem_Ioo.mpr ⟨?_, ?_⟩) v hgt h2
    · rw [hm]; linarith
    · rw [hm]; linarith
  exact ⟨fun x : M => Ψ (Int.toNat ⌊g x + 1 / 4⌋) x, hPsm, hP0, hPtr⟩

end

end Work.Drive.RayTube
