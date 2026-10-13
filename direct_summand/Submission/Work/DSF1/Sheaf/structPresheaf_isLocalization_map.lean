import Mathlib
import Submission.Work.DSF1.Sheaf.CechStruct

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

set_option linter.style.haveILetI false

namespace Work.DSF1.Sheaf

theorem structPresheaf_isLocalization_map {X : AlgebraicGeometry.Scheme} {W : X.Opens}
    (hW : AlgebraicGeometry.IsAffineOpen W) (h : ↥(X.presheaf.obj (Opposite.op ⊤))) :
    (∀ z : (Work.DSF1.Sheaf.structPresheaf X).obj (Opposite.op (W ⊓ X.basicOpen h)),
      ∃ (k : ℕ) (t : (Work.DSF1.Sheaf.structPresheaf X).obj (Opposite.op W)),
        ((Work.DSF1.Sheaf.structPresheaf X).map
          (CategoryTheory.homOfLE (inf_le_left : W ⊓ X.basicOpen h ≤ W)).op).hom t = h ^ k • z) ∧
    (∀ t : (Work.DSF1.Sheaf.structPresheaf X).obj (Opposite.op W),
      ((Work.DSF1.Sheaf.structPresheaf X).map
        (CategoryTheory.homOfLE (inf_le_left : W ⊓ X.basicOpen h ≤ W)).op).hom t = 0 →
        ∃ k : ℕ, h ^ k • t = 0) := by
  -- Work with `V = W ⊓ D(h)` and `f = h|_W`, so that `Γ(X, V) = Γ(X, W)_{h|_W}`.
  let V : X.Opens := W ⊓ X.basicOpen h
  let f : Γ(X, W) := X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op h
  have hf : X.basicOpen f = V := Scheme.basicOpen_res (X := X) h (homOfLE (le_top : W ≤ ⊤)).op
  let iV : V ⟶ W := homOfLE (inf_le_left : V ≤ W)
  -- Record the relevant algebra structures so that the module actions are the ones from
  -- `structPresheaf` and the ring map `Γ(X, W) ⟶ Γ(X, V)` is the restriction.
  letI : Algebra Γ(X, ⊤) Γ(X, W) := (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom.toAlgebra
  letI : Algebra Γ(X, ⊤) Γ(X, V) := (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom.toAlgebra
  letI : Algebra Γ(X, W) Γ(X, V) := (X.presheaf.map iV.op).hom.toAlgebra
  -- `Γ(X, V)` is the localization of `Γ(X, W)` at `f`.
  haveI : IsLocalization.Away f Γ(X, V) := hW.isLocalization_of_eq_basicOpen f iV hf.symm
  -- Restate the goal in the underlying types.
  change (∀ z : Γ(X, V), ∃ (k : ℕ) (t : Γ(X, W)),
      (algebraMap Γ(X, W) Γ(X, V)) t = h ^ k • z) ∧
    (∀ t : Γ(X, W), (algebraMap Γ(X, W) Γ(X, V)) t = 0 → ∃ k : ℕ, h ^ k • t = 0)
  -- The restriction maps are compatible.
  have hθf' : (X.presheaf.map iV.op).hom f
      = (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom h := by
    dsimp only [f, iV]
    rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
    congr 1
  have hθf : (algebraMap Γ(X, W) Γ(X, V)) f = (algebraMap Γ(X, ⊤) Γ(X, V)) h := hθf'
  have hkey : ∀ n : ℕ, (algebraMap Γ(X, W) Γ(X, V)) (f ^ n)
      = (algebraMap Γ(X, ⊤) Γ(X, V)) (h ^ n) := by
    intro n
    rw [map_pow, hθf, map_pow]
  -- The module action of `Γ(X, ⊤)` is multiplication via the algebra map.
  have hsmulV : ∀ n : ℕ, ∀ z : Γ(X, V), h ^ n • z
      = (algebraMap Γ(X, ⊤) Γ(X, V)) (h ^ n) * z := by
    intro n z
    rw [Algebra.smul_def]
  have hsmulW : ∀ n : ℕ, ∀ t : Γ(X, W), h ^ n • t = f ^ n * t := by
    intro n t
    rw [Algebra.smul_def]
    congr 1
    rw [RingHom.algebraMap_toAlgebra, map_pow]
  constructor
  · -- Surjectivity: every section over `V` is `t / hᵏ`.
    intro z
    obtain ⟨⟨a, c⟩, hz0⟩ := IsLocalization.surj (Submonoid.powers f) z
    have hz : z * (algebraMap Γ(X, W) Γ(X, V)) (c : Γ(X, W))
        = (algebraMap Γ(X, W) Γ(X, V)) a := hz0
    obtain ⟨n, hn⟩ : ∃ n, f ^ n = (c : Γ(X, W)) :=
      (Submonoid.mem_powers_iff (M := Γ(X, W)) (c : Γ(X, W)) f).mp c.2
    refine ⟨n, a, ?_⟩
    rw [hz.symm, ← hn, hkey n, hsmulV n z]
    exact mul_comm _ _
  · -- Every section killed by restriction is killed by some power of `h`.
    intro t ht
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers f) Γ(X, V)
      (x := t) (y := 0)).mp (by rw [ht, map_zero])
    obtain ⟨n, hn⟩ : ∃ n, f ^ n = (c : Γ(X, W)) :=
      (Submonoid.mem_powers_iff (M := Γ(X, W)) (c : Γ(X, W)) f).mp c.2
    refine ⟨n, ?_⟩
    have hft : f ^ n * t = 0 := by simpa [← hn] using hc
    rw [hsmulW n t]
    exact hft

end Work.DSF1.Sheaf
