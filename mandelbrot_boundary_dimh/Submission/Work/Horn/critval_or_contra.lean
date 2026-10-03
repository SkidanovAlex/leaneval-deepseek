import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.localBiholo_source_subset
import Submission.Work.Horn.isLocalHomeomorphOn_subtypeMap
import Submission.Work.Horn.isCoveringMap_subtypeMap
import Submission.Work.Repel.invFunOn_differentiableOn

namespace Work.Horn

open Set Filter Topology

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- A covering self-map of a path connected, simply connected space is injective. -/
private theorem injective_of_isCoveringMap_self' {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] [SimplyConnectedSpace X] {p : X → X} (hcov : IsCoveringMap p) :
    Function.Injective p := by
  intro u v huv
  have : Subsingleton (Path.Homotopic.Quotient (p u) (p v)) := inferInstance
  have hgoal : hcov.monodromy (Path.Homotopic.Quotient.refl (p v)) (⟨u, huv⟩ : p ⁻¹' {p v}) =
      ⟨v, rfl⟩ := by
    refine hcov.monodromy_eq_of_map_eq (γ := Path.Homotopic.Quotient.refl (p v))
      (Γ := Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath u v)) ?_
    exact Subsingleton.elim _ _
  rw [hcov.monodromy_refl] at hgoal
  exact Subtype.ext_iff.mp hgoal

/-- **Critical value or contradiction.**

`G` is holomorphic on the bounded simply connected domain `B`, maps `B` into itself, is proper and
onto `B`, and admits an Abel (Fatou) coordinate `Φ` on `B` for the unit translation,
`Φ (G z) = Φ z + 1`.  On a `G`-invariant open set `P ⊆ B` the coordinate `Φ` is injective and its
image contains the tail of every horizontal strip, and every `G`-orbit in `B` eventually enters `P`.
Then `G` has a critical point in `B`.

The proof is by contradiction.  If `deriv G` never vanished on `B`, then `G|_B` would be a proper
local homeomorphism of `B`, hence a covering self-map, hence injective (a covering of a path
connected simply connected space with connected total space is trivial, so its degree is `1`).
Since every orbit enters the `Φ`-injective set `P`, this makes `Φ` injective on all of `B`; and
since `G` is onto, the strip condition together with the translation equivariance propagates to
`Φ '' B = ℂ`.  So `Φ` would be a biholomorphism from the bounded domain `B` onto `ℂ`: its inverse
is holomorphic (inverse function theorem) and bounded (as `B` is bounded), hence constant by
Liouville — contradiction. -/
theorem critval_or_contra {G : ℂ → ℂ} {B P : Set ℂ} {Φ : ℂ → ℂ}
    (hBopen : IsOpen B) (hBconn : IsConnected B) (hBsc : SimplyConnectedSpace B)
    (hbdd : Bornology.IsBounded B)
    (hG : ∀ z ∈ B, DifferentiableAt ℂ G z)
    (hmap : Set.MapsTo G B B)
    (hproper : ∀ L : Set ℂ, L ⊆ B → IsCompact L → IsCompact (B ∩ G ⁻¹' L))
    (hsurj : B ⊆ G '' B)
    (hPopen : IsOpen P) (hPsub : P ⊆ B) (hPmap : Set.MapsTo G P P)
    (hΦ : DifferentiableOn ℂ Φ B) (habel : ∀ z ∈ B, Φ (G z) = Φ z + 1)
    (hΦinj : Set.InjOn Φ P)
    (hstrip : ∀ b : ℝ, ∃ C : ℝ, ∀ w : ℂ, C < w.re → |w.im| ≤ b → ∃ z ∈ P, Φ z = w)
    (henter : ∀ z ∈ B, ∃ n : ℕ, G^[n] z ∈ P) :
    ∃ z : ℂ, z ∈ B ∧ deriv G z = 0 := by
  by_contra hcon
  push Not at hcon
  -- `G` has no critical point on `B`, so `G|_B` is a proper local homeomorphism.
  have hGdiffOn : DifferentiableOn ℂ G B := fun z hz => (hG z hz).differentiableWithinAt
  have hfold : ∀ c ∈ B, ∃ e : OpenPartialHomeomorph ℂ ℂ, c ∈ e.source ∧ e.source ⊆ B ∧
      (⇑e : ℂ → ℂ) = G := fun c hc =>
    localBiholo_source_subset hBopen hBopen subset_rfl hGdiffOn hc (hcon c hc)
  have hlo := isLocalHomeomorphOn_subtypeMap hBopen hmap hfold
  have hcov := isCoveringMap_subtypeMap hBopen hmap hproper hlo
  haveI : PathConnectedSpace B :=
    isPathConnected_iff_pathConnectedSpace.mp ((hBopen.isConnected_iff_isPathConnected).mp hBconn)
  haveI : SimplyConnectedSpace B := hBsc
  -- Hence `G|_B` is injective, so `G` is injective on `B`.
  have hinjF : Function.Injective (fun x : B => (⟨G x.1, hmap x.2⟩ : B)) :=
    injective_of_isCoveringMap_self' hcov
  have hGinj : Set.InjOn G B := by
    intro u hu v hv huv
    have h1 : (⟨u, hu⟩ : B) = ⟨v, hv⟩ := hinjF (Subtype.ext huv)
    exact Subtype.ext_iff.mp h1
  -- The Abel equation, iterated.
  have hiter : ∀ (n : ℕ) (z : ℂ), z ∈ B → G^[n] z ∈ B ∧ Φ (G^[n] z) = Φ z + (n : ℂ) := by
    intro n
    induction n with
    | zero => intro z hz; exact ⟨hz, by simp⟩
    | succ n ih =>
      intro z hz
      obtain ⟨hmem, hval⟩ := ih z hz
      rw [Function.iterate_succ_apply']
      exact ⟨hmap hmem, by rw [habel (G^[n] z) hmem, hval]; push_cast; ring⟩
  -- Since every orbit enters `P`, `Φ` is injective on all of `B`.
  have hΦinjB : Set.InjOn Φ B := by
    intro u hu v hv huv
    obtain ⟨n₁, hn₁⟩ := henter u hu
    obtain ⟨n₂, hn₂⟩ := henter v hv
    have hNu : G^[max n₁ n₂] u ∈ P := by
      rw [← Nat.sub_add_cancel (le_max_left n₁ n₂), Function.iterate_add_apply]
      exact (hPmap.iterate (max n₁ n₂ - n₁)) hn₁
    have hNv : G^[max n₁ n₂] v ∈ P := by
      rw [← Nat.sub_add_cancel (le_max_right n₁ n₂), Function.iterate_add_apply]
      exact (hPmap.iterate (max n₁ n₂ - n₂)) hn₂
    have hvalU := (hiter (max n₁ n₂) u hu).2
    have hvalV := (hiter (max n₁ n₂) v hv).2
    have heq : Φ (G^[max n₁ n₂] u) = Φ (G^[max n₁ n₂] v) := by rw [hvalU, hvalV, huv]
    have hGu : G^[max n₁ n₂] u = G^[max n₁ n₂] v := hΦinj hNu hNv heq
    exact (hGinj.iterate hmap (max n₁ n₂)) hu hv hGu
  -- The strip condition plus the equivariance gives `Φ '' B = ℂ`.
  have hΦsurj : Φ '' B = univ := by
    ext w
    simp only [mem_image, mem_univ, iff_true]
    -- `Φ '' B` is invariant under subtracting `1` (using that `G` is onto `B`).
    have hstep : ∀ w : ℂ, w ∈ Φ '' B → w - 1 ∈ Φ '' B := by
      rintro w ⟨z, hzB, rfl⟩
      obtain ⟨z', hz'B, hz'⟩ := hsurj hzB
      exact ⟨z', hz'B, by rw [← hz', habel z' hz'B]; ring⟩
    have hsub : ∀ (n : ℕ) (w : ℂ), w ∈ Φ '' B → w - (n : ℂ) ∈ Φ '' B := by
      intro n
      induction n with
      | zero => intro w hw; simpa using hw
      | succ n ih =>
        intro w hw
        have : w - ((n + 1 : ℕ) : ℂ) = (w - 1) - (n : ℂ) := by push_cast; ring
        rw [this]
        exact ih (w - 1) (hstep w hw)
    obtain ⟨C, hC⟩ := hstrip (|w.im| + 1)
    obtain ⟨N, hN⟩ : ∃ N : ℕ, C < w.re + N := by
      obtain ⟨N, hN⟩ := exists_nat_gt (C - w.re)
      exact ⟨N, by linarith⟩
    have hmem : ∃ z ∈ P, Φ z = w + (N : ℂ) :=
      hC (w + (N : ℂ)) (by simp [hN]) (by simp)
    obtain ⟨z, hzP, hz⟩ := hmem
    have hw : w = (w + (N : ℂ)) - (N : ℂ) := by ring
    rw [hw, ← hz]
    exact hsub N (Φ z) ⟨z, hPsub hzP, rfl⟩
  -- The inverse of `Φ` is holomorphic (inverse function theorem for injective holomorphic maps).
  have hψdiff : DifferentiableOn ℂ (Function.invFunOn Φ B) (Φ '' B) :=
    Work.Repel.invFunOn_differentiableOn hBopen hΦinjB hΦ
  have hψdiff' : Differentiable ℂ (Function.invFunOn Φ B) := by
    rw [← differentiableOn_univ, ← hΦsurj]
    exact hψdiff
  -- It takes values in the bounded set `B`, so Liouville makes it constant.
  have hψmem : Set.range (Function.invFunOn Φ B) ⊆ B := by
    rintro _ ⟨w, rfl⟩
    have hw : w ∈ Φ '' B := by rw [hΦsurj]; exact mem_univ w
    exact Function.invFunOn_mem (by simpa using hw)
  have hbddψ : Bornology.IsBounded (Set.range (Function.invFunOn Φ B)) := hbdd.subset hψmem
  obtain ⟨c, hc⟩ := hψdiff'.exists_const_forall_eq_of_bounded hbddψ
  have hconst : ∀ w : ℂ, w = Φ c := by
    intro w
    have h1 : Φ (Function.invFunOn Φ B w) = w :=
      Function.invFunOn_eq (by
        have hw : w ∈ Φ '' B := by rw [hΦsurj]; exact mem_univ w
        simpa using hw)
    rw [hc w] at h1
    exact h1.symm
  have hbad : (Φ c + 1 : ℂ) = Φ c := hconst (Φ c + 1)
  have : (1 : ℂ) = 0 := by linear_combination hbad
  exact one_ne_zero this

end Work.Horn
