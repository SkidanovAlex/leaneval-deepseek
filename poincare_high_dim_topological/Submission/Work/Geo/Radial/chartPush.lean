import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Geo.Radial.Basic

/-!
# Conjugating the radial push through a cube chart

Area `A7` (`Geo/Radial+Conn-rel`).  This file contains the derived facts about a cube chart
`c : PL.CubeChart n M` and a chart push that the proof of blueprint C1
(`Work.Geo.Radial.conn_minus_cube`) needs:

* `mem_openCube`, `mem_closedCube`, `openCube_mono`, `closedCube_subset_openCube`,
  `closedCube_subset_openCube_of_lt` : elementary cube API (the sup-norm cubes of the frozen
  vocabulary `PL`);
* `chart_inj` : `c.toFun` is injective on `openCube 1`;
* `chartPush_notMem_of_notMem` : a chart push which is radial about a point `q` of the closed
  `β`-cube preserves the complement of the chart image of that cube (this is what makes the
  homotopy `s ↦ h s ∘ f` stay inside the complement);
* `chartPush_avoids_openCube` : the first push (centred at the origin, pushing everything at
  distance `≥ ε ≤ β` beyond `R > τ + m`) moves the complement of the closed `β`-cube off the
  chart image of the open `τ`-cube;
* `chartPush2_avoids_closedCube` : the second push (centred at a point `q` missed by the image,
  pushing beyond `R₂ > β + m`) moves a set avoiding `c '' ocubeAround q ε` off the chart image of
  the closed `β`-cube.
-/

open Set Metric
open scoped Topology

namespace Work.Geo.Radial


@[simp] theorem mem_openCube {n : ℕ} {r : ℝ} {y : PL.E n} :
    y ∈ PL.openCube r ↔ ∀ i, |y i| < r := by simp [PL.openCube]

@[simp] theorem mem_closedCube {n : ℕ} {r : ℝ} {y : PL.E n} :
    y ∈ PL.closedCube r ↔ ∀ i, |y i| ≤ r := by simp [PL.closedCube]

theorem openCube_mono {n : ℕ} {r r' : ℝ} (h : r ≤ r') :
    PL.openCube (n := n) r ⊆ PL.openCube r' :=
  fun _ hy i => lt_of_lt_of_le (hy i) h

theorem closedCube_subset_openCube {n : ℕ} {r : ℝ} (h : r < 1) :
    PL.closedCube (n := n) r ⊆ PL.openCube 1 :=
  fun _ hy i => lt_of_le_of_lt (hy i) h

theorem closedCube_subset_openCube_of_lt {n : ℕ} {r r' : ℝ} (h : r < r') :
    PL.closedCube (n := n) r ⊆ PL.openCube r' :=
  fun _ hy i => lt_of_le_of_lt (hy i) h

/-- Injectivity of `c.toFun` on the unit cube. -/
theorem chart_inj {n : ℕ} {M : Type*} [TopologicalSpace M] (c : PL.CubeChart n M)
    {a b : PL.E n} (ha : a ∈ PL.openCube 1) (hb : b ∈ PL.openCube 1)
    (h : c.toFun a = c.toFun b) : a = b := by
  have h1 : ((PL.openCube 1).domRestrict c.toFun) ⟨a, ha⟩ =
      ((PL.openCube 1).domRestrict c.toFun) ⟨b, hb⟩ := h
  exact congrArg Subtype.val (c.emb.isEmbedding.injective h1)

theorem chartPush_notMem_of_notMem {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : PL.CubeChart n M) {β m τ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {q : PL.E n}
    (hq : ∀ i, |q i| ≤ m) (hmβ : m ≤ β) (hτ : β < τ) (hτ1 : τ ≤ 1)
    {H : PL.E n ≃ₜ PL.E n}
    (hlam : ∀ y, ∃ lam : ℝ, 1 ≤ lam ∧ ∀ i, H y i - q i = lam * (y i - q i))
    {h : M ≃ₜ M} (hid : ∀ p, p ∉ c.toFun '' PL.openCube τ → h p = p)
    (hchart : ∀ y ∈ PL.openCube τ, H y ∈ PL.openCube 1 ∧ h (c.toFun y) = c.toFun (H y))
    {p : M} (hp : p ∉ c.toFun '' PL.closedCube β) :
    h p ∉ c.toFun '' PL.closedCube β := by
  by_cases hpc : p ∈ c.toFun '' PL.openCube τ
  · obtain ⟨y, hy, rfl⟩ := hpc
    have hyc : y ∉ PL.closedCube β := fun hc => hp ⟨y, hc, rfl⟩
    obtain ⟨lam, hlam1, hlam2⟩ := hlam y
    have hHy : H y ∉ PL.closedCube β := scale_notMem_closedCube hβ0 hq hmβ hyc hlam1 hlam2
    rw [(hchart y hy).2]
    intro hmem
    obtain ⟨y', hy'c, hy'eq⟩ := hmem
    have hy'1 : y' ∈ PL.openCube 1 := closedCube_subset_openCube hβ1 hy'c
    have : y' = H y := chart_inj c hy'1 (hchart y hy).1 hy'eq
    exact hHy (this ▸ hy'c)
  · rw [hid p hpc]
    refine fun hmem => hpc (Set.image_mono ?_ hmem)
    intro y hy
    rw [mem_closedCube] at hy
    rw [mem_openCube]
    exact fun i => lt_of_le_of_lt (hy i) hτ

end Work.Geo.Radial

namespace Work.Geo.Radial

/-- Push 1: the chart push (centred at the origin, parameters `ε ≤ β`, `R > τ + m`) sends the
complement of the closed `β`-cube off the chart image of the open `τ`-cube. -/
theorem chartPush_avoids_openCube {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : PL.CubeChart n M) {β τ τ' m ε R : ℝ} (hβ : β < 1) (hm : 0 ≤ m)
    (hεβ : ε ≤ β) (hRτ : τ + m < R) (hττ' : τ < τ') (hτ'1 : τ' ≤ 1)
    {H : PL.E n ≃ₜ PL.E n}
    (hHpush : ∀ y, y ∉ ocubeAround (0 : PL.E n) ε → H y ∉ ocubeAround (0 : PL.E n) R)
    {h : M ≃ₜ M} (hid : ∀ p, p ∉ c.toFun '' PL.openCube τ' → h p = p)
    (hchart : ∀ y ∈ PL.openCube τ', H y ∈ PL.openCube 1 ∧ h (c.toFun y) = c.toFun (H y))
    {p : M} (hp : p ∉ c.toFun '' PL.closedCube β) : h p ∉ c.toFun '' PL.openCube τ := by
  have hτ1 : τ ≤ 1 := le_trans (le_of_lt hττ') hτ'1
  have hτR : τ < R := lt_of_le_of_lt (by linarith) hRτ
  by_cases hpc : p ∈ c.toFun '' PL.openCube τ'
  · obtain ⟨y, hy, rfl⟩ := hpc
    have hyc : y ∉ PL.closedCube β := fun hc => hp ⟨y, hc, rfl⟩
    rw [mem_closedCube] at hyc
    simp only [not_forall, not_le] at hyc
    obtain ⟨i₀, hi₀⟩ := hyc
    have hyε : y ∉ ocubeAround (0 : PL.E n) ε := by
      rw [ocubeAround_zero, mem_openCube]
      intro hcon
      exact absurd (hcon i₀) (not_lt.mpr (le_trans hεβ (le_of_lt hi₀)))
    have hHR : H y ∉ ocubeAround (0 : PL.E n) R := hHpush y hyε
    rw [ocubeAround_zero, mem_openCube] at hHR
    simp only [not_forall, not_lt] at hHR
    obtain ⟨i₁, hi₁⟩ := hHR
    rw [(hchart y hy).2]
    intro hmem
    obtain ⟨y', hy', hy'eq⟩ := hmem
    have hy'1 : y' ∈ PL.openCube 1 := openCube_mono hτ1 hy'
    have : y' = H y := chart_inj c hy'1 (hchart y hy).1 hy'eq
    subst this
    rw [mem_openCube] at hy'
    exact absurd (hy' i₁) (not_lt.mpr (le_trans (le_of_lt hτR) hi₁))
  · rw [hid p hpc]
    exact fun hmem => hpc (Set.image_mono (openCube_mono (le_of_lt hττ')) hmem)

/-- Push 2: the chart push centred at a missed point `q` (parameters `R₂ > β + m`) sends a set
avoiding `c '' ocubeAround q ε` off the chart image of the closed `β`-cube. -/
theorem chartPush2_avoids_closedCube {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : PL.CubeChart n M) {β m τ' R₂ ε : ℝ} (hβ : β < 1) {q : PL.E n} (hq : ∀ i, |q i| ≤ m)
    (hβm : β + m < R₂) (hτ' : τ' ≤ 1) (hβτ' : β < τ')
    {H : PL.E n ≃ₜ PL.E n}
    (hHpush : ∀ y, y ∉ ocubeAround q ε → H y ∉ ocubeAround q R₂)
    {h : M ≃ₜ M} (hid : ∀ p, p ∉ c.toFun '' PL.openCube τ' → h p = p)
    (hchart : ∀ y ∈ PL.openCube τ', H y ∈ PL.openCube 1 ∧ h (c.toFun y) = c.toFun (H y))
    {p : M} (hp : p ∉ c.toFun '' ocubeAround q ε) :
    h p ∉ c.toFun '' PL.closedCube β := by
  by_cases hpc : p ∈ c.toFun '' PL.openCube τ'
  · obtain ⟨y, hy, rfl⟩ := hpc
    have hyε : y ∉ ocubeAround q ε := fun hcon => hp ⟨y, hcon, rfl⟩
    have hHR : H y ∉ ocubeAround q R₂ := hHpush y hyε
    have hHc : H y ∉ PL.closedCube β := fun hcon =>
      hHR (closedCube_subset_ocubeAround hq hβm hcon)
    rw [(hchart y hy).2]
    intro hmem
    obtain ⟨y', hy'c, hy'eq⟩ := hmem
    have hy'1 : y' ∈ PL.openCube 1 := closedCube_subset_openCube hβ hy'c
    have : y' = H y := chart_inj c hy'1 (hchart y hy).1 hy'eq
    exact hHc (this ▸ hy'c)
  · rw [hid p hpc]
    exact fun hmem => hpc (Set.image_mono (closedCube_subset_openCube_of_lt hβτ') hmem)

end Work.Geo.Radial
