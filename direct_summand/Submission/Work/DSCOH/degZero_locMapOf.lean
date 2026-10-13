import Mathlib
import Submission.Work.DSCOH.Basic

namespace Work.DSCOH

/-- The map induced on the localizations commutes with division by `(∏_{i∈S} Xᵢ)^k` and with
the structure maps `toLoc`: it sends `m/X_S^k` to `φ(m)/X_S^k`. -/
private lemma locMapOf_divPow_toLoc {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module (Poly A n) N] [IsScalarTower A (Poly A n) N]
    (φ : M →ₗ[Poly A n] N) (S : Finset (Fin n)) (k : ℕ) (m : M) :
    locMapOf φ S (divPow (M := M) S k (toLoc (M := M) S m)) =
      divPow (M := N) S k (toLoc (M := N) S (φ m)) := by
  unfold locMapOf divPow toLoc
  simp only [LinearMap.restrictScalars_apply, LocalizedModule.mkLinearMap_apply,
    LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk]
  rw [IsLocalizedModule.map_LocalizedModules]

theorem degZero_locMapOf {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M)
    {N : Type*} [AddCommGroup N] [Module A N] [Module (Poly A n) N] [IsScalarTower A (Poly A n) N]
    (𝒩 : ℕ → Submodule A N) (φ : M →ₗ[Poly A n] N)
    (hφ : ∀ d, Submodule.map (φ.restrictScalars A) (ℳ d) ≤ 𝒩 d) (S : Finset (Fin n)) :
    ∀ x ∈ degZero ℳ S, locMapOf φ S x ∈ degZero 𝒩 S := by
  -- It suffices that `locMapOf φ S` maps every piece `ℳ_{k·|S|}/X_S^k` into `degZero 𝒩 S`.
  have key : ∀ k : ℕ, Submodule.map ((locMapOf φ S).restrictScalars A)
      (Submodule.map ((divPow (M := M) S k).comp (toLoc (M := M) S)) (ℳ (k * S.card)))
        ≤ degZero 𝒩 S := by
    intro k
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨m, hm, rfl⟩ := Submodule.mem_map.mp hy
    change locMapOf φ S (divPow (M := M) S k (toLoc (M := M) S m)) ∈ degZero 𝒩 S
    rw [locMapOf_divPow_toLoc]
    refine Submodule.mem_iSup_of_mem k (Submodule.mem_map_of_mem (f := (divPow (M := N) S k).comp
      (toLoc (M := N) S)) (p := 𝒩 (k * S.card)) ?_)
    exact hφ (k * S.card) (Submodule.mem_map_of_mem (f := φ.restrictScalars A)
      (p := ℳ (k * S.card)) hm)
  have hmain : Submodule.map ((locMapOf φ S).restrictScalars A) (degZero ℳ S) ≤ degZero 𝒩 S := by
    rw [degZero, Submodule.map_iSup]
    exact iSup_le key
  intro x hx
  exact hmain (Submodule.mem_map_of_mem (f := (locMapOf φ S).restrictScalars A)
    (p := degZero ℳ S) hx)

end Work.DSCOH
