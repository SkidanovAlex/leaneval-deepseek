/-
The BN-pair structure of `Sz(2^(2n+1))`: the Borel subgroup is the normalizer of the Suzuki
2-group `U` inside `SzModel n`.

Since `B = U ⋊ T` normalizes `U`, and `w ∉ N(U)` (because `w U w` is lower unitriangular
whereas `U` is upper unitriangular), the Bruhat decomposition `Sz = B ∪ B w B` shows that no
element of the double coset `B w B` normalizes `U`.
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.Sz.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

open Matrix LeanEval.GroupTheory.Defs
open scoped Pointwise

namespace Submission.Sz

/-- The Borel subgroup normalizes the Suzuki 2-group. -/
lemma szBorel_le_normalizer_szTwoGroup (n : ℕ) :
    szBorel n ≤ Subgroup.normalizer (szTwoGroup n : Set (GL (Fin 4) (SzField n))) := by
  rw [szBorel]
  refine sup_le ?_ (szTgHom_range_le_normalizer n)
  rw [Subgroup.le_normalizer_iff]
  exact fun h hh k hk => (szTwoGroup n).mul_mem ((szTwoGroup n).mul_mem hh hk)
    ((szTwoGroup n).inv_mem hh)

/-- `w` does not normalize the Suzuki 2-group: `w U w` is lower unitriangular while `U` is
upper unitriangular. -/
lemma szWg_conj_szTwoGroup_ne (n : ℕ) :
    (szTwoGroup n).map (MulAut.conj (szWg n)).toMonoidHom ≠ szTwoGroup n := by
  intro h
  have hmem : szUg n 1 0 ∈ (szTwoGroup n).map (MulAut.conj (szWg n)).toMonoidHom := by
    rw [h]; exact ⟨1, 0, rfl⟩
  rw [Subgroup.mem_map] at hmem
  obtain ⟨u, hu, huA⟩ := hmem
  obtain ⟨a, b, rfl⟩ := hu
  have hwinv : (szWg n)⁻¹ = szWg n := inv_eq_of_mul_eq_one_right (szWg_mul_self n)
  have hconj : MulAut.conj (szWg n) (szUg n a b) = szWg n * szUg n a b * szWg n := by
    rw [MulAut.conj_apply, hwinv]
  have h0 : ((MulAut.conj (szWg n) (szUg n a b) : GL (Fin 4) (SzField n)) :
      Matrix (Fin 4) (Fin 4) (SzField n)) 0 1 = 0 := by
    rw [hconj]
    exact szWg_conj_szUg_apply_of_gt n a b (by decide)
  have huA' : (MulAut.conj (szWg n) (szUg n a b) : GL (Fin 4) (SzField n)) = szUg n 1 0 := huA
  have h1 : ((szUg n 1 0 : GL (Fin 4) (SzField n)) :
      Matrix (Fin 4) (Fin 4) (SzField n)) 0 1 = 1 := by
    simp [szUg_coe, szU]
  rw [← huA'] at h1
  rw [h0] at h1
  exact one_ne_zero h1.symm

/-- The normalizer of the Suzuki 2-group inside `SzModel n` is the Borel subgroup. -/
theorem normalizer_szTwoGroup_inf_szModel (n : ℕ) :
    Subgroup.normalizer (szTwoGroup n : Set (GL (Fin 4) (SzField n))) ⊓ SzModel n =
      szBorel n := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgN, hgS⟩ := hg
    have hmem : g ∈ szBwBSet n := by
      rw [szModel_eq_szBwBSubgroup' n] at hgS
      exact hgS
    rcases hmem with hmem | hmem
    · exact hmem
    · exfalso
      obtain ⟨b₁, hb₁, b₂, hb₂, hgb⟩ := (mem_szBwB n g).mp hmem
      have hb1N := szBorel_le_normalizer_szTwoGroup n hb₁
      have hb2N := szBorel_le_normalizer_szTwoGroup n hb₂
      have hwN : szWg n ∈ Subgroup.normalizer (szTwoGroup n : Set (GL (Fin 4) (SzField n))) := by
        have h := (Subgroup.normalizer (szTwoGroup n : Set (GL (Fin 4) (SzField n)))).mul_mem
          ((Subgroup.normalizer (szTwoGroup n : Set (GL (Fin 4) (SzField n)))).mul_mem
            ((Subgroup.normalizer (szTwoGroup n : Set (GL (Fin 4) (SzField n)))).inv_mem hb1N) hgN)
          ((Subgroup.normalizer (szTwoGroup n : Set (GL (Fin 4) (SzField n)))).inv_mem hb2N)
        convert h using 1
        rw [← hgb]; group
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hwN
      exact szWg_conj_szTwoGroup_ne n hwN
  · intro g hg
    exact ⟨szBorel_le_normalizer_szTwoGroup n hg, szBorel_le_szModel n hg⟩

/-- The Borel subgroup is a maximal subgroup of `SzModel n` (this is the Bruhat
decomposition, together with `N_G(U) = B`). -/
theorem szBorel_isCoatom (n : ℕ) :
    ∀ H : Subgroup (GL (Fin 4) (SzField n)), szBorel n < H → H ≤ SzModel n →
      H = SzModel n := by
  intro H hlt hHS
  have hBH : szBorel n ≤ H := hlt.le
  have hne : H ≠ szBorel n := hlt.ne'
  obtain ⟨g, hgH, hgB⟩ : ∃ g ∈ H, g ∉ szBorel n := by
    by_contra h
    push_neg at h
    exact hne (le_antisymm (fun x hx => h x hx) hBH)
  have hgS : g ∈ SzModel n := hHS hgH
  have hmem : g ∈ szBwBSet n := by
    rw [szModel_eq_szBwBSubgroup' n] at hgS
    exact hgS
  rcases hmem with hmem | hmem
  · exact absurd hmem hgB
  · obtain ⟨b₁, hb₁, b₂, hb₂, hgb⟩ := (mem_szBwB n g).mp hmem
    have hwH : szWg n ∈ H := by
      have h := H.mul_mem (H.mul_mem (H.inv_mem (hBH hb₁)) hgH) (H.inv_mem (hBH hb₂))
      convert h using 1
      rw [← hgb]; group
    apply le_antisymm hHS
    intro x hx
    rw [szModel_eq_szBwBSubgroup' n] at hx
    rcases hx with hx | hx
    · exact hBH hx
    · obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := (mem_szBwB n x).mp hx
      exact H.mul_mem (H.mul_mem (hBH hc₁) hwH) (hBH hc₂)

/-- `(szWg n)⁻¹ = szWg n`. -/
lemma szWg_inv_eq (n : ℕ) :
    (szWg n)⁻¹ = szWg n := inv_eq_of_mul_eq_one_right (szWg_mul_self n)

/-- `t * w = w * t⁻¹` for a torus element `t`. -/
lemma szTorus_mul_szWg (n : ℕ) (x : (SzField n)ˣ) :
    szTg n x * szWg n = szWg n * (szTg n x)⁻¹ := by
  calc szTg n x * szWg n
      = szWg n * (szWg n * szTg n x * szWg n) := by
        rw [show szWg n * (szWg n * szTg n x * szWg n) = szTg n x * szWg n from by
          rw [← mul_assoc, ← mul_assoc, szWg_mul_self, one_mul]]
    _ = szWg n * (szTg n x)⁻¹ := by rw [szWg_conj_szTg, szTg_inv]

lemma szTorus_map_conj_szWg (n : ℕ) :
    (szTgHom n).range.map (MulAut.conj (szWg n)).toMonoidHom = (szTgHom n).range := by
  have hwinv := szWg_inv_eq n
  apply le_antisymm
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨x, rfl⟩ := hz
    have h1 : (MulAut.conj (szWg n)).toMonoidHom (szTgHom n x) = szTg n x⁻¹ := by
      show MulAut.conj (szWg n) (szTg n x) = szTg n x⁻¹
      rw [MulAut.conj_apply, hwinv]; exact szWg_conj_szTg n x
    rw [h1]
    exact ⟨x⁻¹, rfl⟩
  · intro y hy
    obtain ⟨x, rfl⟩ := hy
    refine Subgroup.mem_map.mpr ⟨szTg n x⁻¹, ⟨x⁻¹, rfl⟩, ?_⟩
    have h1 : (MulAut.conj (szWg n)).toMonoidHom (szTgHom n x⁻¹) = szTg n x := by
      show MulAut.conj (szWg n) (szTg n x⁻¹) = szTg n x
      rw [MulAut.conj_apply, hwinv, szWg_conj_szTg, inv_inv]
    exact h1

/-- `w B w = (w U w) T`. -/
lemma szBorel_map_conj_szWg (n : ℕ) :
    (szBorel n).map (MulAut.conj (szWg n)).toMonoidHom =
      (szTwoGroup n).map (MulAut.conj (szWg n)).toMonoidHom ⊔ (szTgHom n).range := by
  rw [szBorel, Subgroup.map_sup, szTorus_map_conj_szWg]

/-- The torus normalizes the opposite unipotent subgroup `w U w`. -/
lemma szTorus_le_normalizer_conj_szTwoGroup (n : ℕ) :
    (szTgHom n).range ≤ Subgroup.normalizer
      ((((szTwoGroup n).map (MulAut.conj (szWg n)).toMonoidHom : Subgroup _)) : Set _) := by
  rw [Subgroup.le_normalizer_iff]
  intro t ht y hy
  obtain ⟨x, rfl⟩ := ht
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨a, b, rfl⟩ := hu
  have htw := szTorus_mul_szWg n x
  refine Subgroup.mem_map.mpr ⟨szTg n x⁻¹ * szUg n a b * szTg n x, ?_, ?_⟩
  · have h := (Subgroup.le_normalizer_iff.mp (szTgHom_range_le_normalizer n)) (szTg n x⁻¹)
      (show szTg n x⁻¹ ∈ (szTgHom n).range from ⟨x⁻¹, rfl⟩) (szUg n a b) ⟨a, b, rfl⟩
    simpa [szTg_inv, inv_inv] using h
  · show MulAut.conj (szWg n) (szTg n x⁻¹ * szUg n a b * szTg n x) =
      szTg n x * MulAut.conj (szWg n) (szUg n a b) * (szTg n x)⁻¹
    rw [szTg_inv, MulAut.conj_apply, MulAut.conj_apply, szWg_inv_eq]
    rw [show szTg n x * (szWg n * szUg n a b * szWg n) * (szTg n x)⁻¹ =
        (szTg n x * szWg n) * szUg n a b * (szTg n x * szWg n)⁻¹ from by
          rw [_root_.mul_inv_rev, szWg_inv_eq]; group]
    rw [htw]
    rw [show (szWg n * (szTg n x)⁻¹) * szUg n a b * (szWg n * (szTg n x)⁻¹)⁻¹ =
        szWg n * ((szTg n x)⁻¹ * szUg n a b * szTg n x) * szWg n from by
          rw [_root_.mul_inv_rev, inv_inv, szWg_inv_eq]; group]

/-- `B ∩ w B w = T`: an element of the Borel that is also in the opposite Borel is diagonal. -/
lemma szBorel_inf_conj_szBorel_eq_torus (n : ℕ) :
    szBorel n ⊓ (szBorel n).map (MulAut.conj (szWg n)).toMonoidHom = (szTgHom n).range := by
  have hbot : (szTwoGroup n).map (MulAut.conj (szWg n)).toMonoidHom ⊓ szBorel n = ⊥ := by
    rw [inf_comm]; exact szBorel_inf_conj_szTwoGroup_eq_bot n
  apply le_antisymm
  · intro x hx
    obtain ⟨hxB, hxw⟩ := hx
    have hle := szTorus_le_normalizer_conj_szTwoGroup n
    have hcoe : (↑((szTwoGroup n).map (MulAut.conj (szWg n)).toMonoidHom ⊔
        (szTgHom n).range) : Set (GL (Fin 4) (SzField n))) =
        (((szTwoGroup n).map (MulAut.conj (szWg n)).toMonoidHom) : Set _) *
          ((szTgHom n).range : Set _) :=
      Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle
    have hx' : x ∈ (szTwoGroup n).map (MulAut.conj (szWg n)).toMonoidHom ⊔
        (szTgHom n).range := by
      rw [szBorel_map_conj_szWg] at hxw
      exact hxw
    have hx'' : x ∈ (((szTwoGroup n).map (MulAut.conj (szWg n)).toMonoidHom :
        Set (GL (Fin 4) (SzField n))) * ((szTgHom n).range : Set (GL (Fin 4) (SzField n)))) := by
      rw [← hcoe]
      exact hx'
    obtain ⟨y, hy, t, ht, hyt⟩ := Set.mem_mul.mp hx''
    have hyB : y ∈ szBorel n := by
      have hyx : y = x * t⁻¹ := by rw [← hyt]; group
      rw [hyx]
      exact (szBorel n).mul_mem hxB ((szBorel n).inv_mem (Subgroup.mem_sup_right ht))
    have hybot : y ∈ (⊥ : Subgroup (GL (Fin 4) (SzField n))) := by
      rw [← hbot]
      exact ⟨hy, hyB⟩
    rw [Subgroup.mem_bot] at hybot
    rw [← hyt, hybot, one_mul]
    exact ht
  · intro x hx
    refine ⟨Subgroup.mem_sup_right hx, ?_⟩
    rw [szBorel_map_conj_szWg]
    exact Subgroup.mem_sup_right hx

/-- For `g ∈ B w B`, the intersection `B ∩ B^g` is conjugate to the torus `T`. -/
lemma szBorel_inf_conj_eq_conj_torus (n : ℕ) {g : GL (Fin 4) (SzField n)}
    (hg : g ∈ szBwB n) :
    ∃ b ∈ szBorel n, szBorel n ⊓ (szBorel n).map (MulAut.conj g).toMonoidHom =
      ((szTgHom n).range).map (MulAut.conj b).toMonoidHom := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (mem_szBwB n g).mp hg
  have hww : szWg n * szWg n = 1 := szWg_mul_self n
  have hwinv := szWg_inv_eq n
  refine ⟨b₁, hb₁, ?_⟩
  ext x
  constructor
  · rintro ⟨hxB, y, hy, hxy⟩
    have hxy' : b₁ * szWg n * b₂ * y * (b₁ * szWg n * b₂)⁻¹ = x := hxy
    refine ⟨b₁⁻¹ * x * b₁, ?_, ?_⟩
    · have hxT : b₁⁻¹ * x * b₁ ∈ szBorel n ⊓
          (szBorel n).map (MulAut.conj (szWg n)).toMonoidHom := by
        refine ⟨(szBorel n).mul_mem ((szBorel n).mul_mem ((szBorel n).inv_mem hb₁) hxB) hb₁, ?_⟩
        refine ⟨b₂ * y * b₂⁻¹, (szBorel n).mul_mem ((szBorel n).mul_mem hb₂ hy)
          ((szBorel n).inv_mem hb₂), ?_⟩
        show MulAut.conj (szWg n) (b₂ * y * b₂⁻¹) = b₁⁻¹ * x * b₁
        rw [MulAut.conj_apply, hwinv, ← hxy', _root_.mul_inv_rev, _root_.mul_inv_rev, hwinv]
        group
      rwa [szBorel_inf_conj_szBorel_eq_torus] at hxT
    · show MulAut.conj b₁ (b₁⁻¹ * x * b₁) = x
      rw [MulAut.conj_apply]
      group
  · rintro ⟨t, ht, htx⟩
    obtain ⟨xx, rfl⟩ := ht
    have ht' : b₁ * szTg n xx * b₁⁻¹ = x := by
      rw [← htx]
      show b₁ * szTg n xx * b₁⁻¹ = MulAut.conj b₁ (szTg n xx)
      rw [MulAut.conj_apply]
    refine ⟨?_, ?_⟩
    · rw [← ht']
      exact (szBorel n).mul_mem ((szBorel n).mul_mem hb₁ (Subgroup.mem_sup_right ⟨xx, rfl⟩))
        ((szBorel n).inv_mem hb₁)
    · refine ⟨b₂⁻¹ * (szWg n * szTg n xx * szWg n) * b₂, ?_, ?_⟩
      · refine (szBorel n).mul_mem ((szBorel n).mul_mem ((szBorel n).inv_mem hb₂) ?_) hb₂
        exact Subgroup.mem_sup_right (by rw [szWg_conj_szTg]; exact ⟨xx⁻¹, rfl⟩)
      · show MulAut.conj (b₁ * szWg n * b₂)
            (b₂⁻¹ * (szWg n * szTg n xx * szWg n) * b₂) = x
        rw [MulAut.conj_apply, _root_.mul_inv_rev, _root_.mul_inv_rev, hwinv, ← ht']
        rw [show b₁ * szWg n * b₂ * (b₂⁻¹ * (szWg n * szTg n xx * szWg n) * b₂) *
              (b₂⁻¹ * (szWg n * b₁⁻¹)) =
            b₁ * (szWg n * szWg n) * szTg n xx * (szWg n * szWg n) * b₁⁻¹ from by group,
          hww]
        simp only [mul_one, one_mul]

end Submission.Sz
