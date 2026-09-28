import Mathlib
import Submission.Work.SSS.baseRowDefs
import Submission.Work.SSS.LESFacts
import Submission.Work.SSS.fg_range_of_ker_le

/-!
# The strata of the image filtration are subquotients of the `E²` page

`Work.SSS.Lem.fgQuot_Psi` is the statement that the `s`-th stratum
`Ψ_s / Ψ_{s-1}` of the image filtration of `H_m(F_m)` (see `Work.SSS.Psi`) is finitely generated
as soon as the `E²` term of bidegree `(s, m-s)` is, i.e. as soon as `Work.SSS.E2quot ξ s (m-s)`
holds.

The proof is the elementary "the associated graded of the filtration is a subquotient of the `E²`
page" argument, in the explicit form given by the exact couple of the filtration:

* `jF ξ (k+1) t : H_n(F_{k+1}) → E¹_{k+1,t}` has kernel `im(H_n(F_k) → H_n(F_{k+1}))`;
* the composite `mkQ (im d¹) ∘ jF ξ (k+1) t` therefore has kernel
  `im(H_n(F_k) → H_n(F_{k+1})) + ker(H_n(F_{k+1}) → H_n(F_{k+2}))`, which is contained in
  `im(H_n(F_k) → H_n(F_{k+1})) + ker(H_n(F_{k+1}) → H_n(F_{n+1}))` — the kernel of the quotient
  map `H_n(F_{k+1}) → Ψ_{k+1}/Ψ_k`;
* the range of `mkQ (im d¹) ∘ jF ξ (k+1) t` sits inside the image of `ker d¹` in the quotient by
  `im d¹`, which is the `E²` term and hence finitely generated.

`Work.SSS.fg_range_of_ker_le` then converts these two facts into finite generation of
`Ψ_{k+1}/Ψ_k`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.SSS.Lem

open CategoryTheory CategoryTheory.Limits

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-- The comparison morphisms of a filtration compose. -/
lemma map_homOfLE_trans (F : ℕ ⥤ ChainComplex (ModuleCat ℤ) ℕ) {a b c : ℕ} (hab : a ≤ b)
    (hbc : b ≤ c) :
    F.map (homOfLE (hab.trans hbc)) = F.map (homOfLE hab) ≫ F.map (homOfLE hbc) := by
  rw [← F.map_comp, homOfLE_comp]

/-- `Psi` unfolds when the index is in range. -/
lemma Psi_of_le (ξ : Filtration C) (m s : ℕ) (h : s ≤ m) :
    Psi ξ m s = (HomologicalComplex.homologyMap (ξ.F.map (homOfLE h)) m).hom.range := by
  simp only [Psi]
  rw [dif_pos h]

/-- The inclusion of `F_j` into `F_{j+1}` followed by the comparison of `F_{j+1}` with `F_n`
equals the comparison of `F_j` with `F_n`. -/
lemma homologyMap_incF_comp (ξ : Filtration C) (n j : ℕ) (hj : j ≤ n) (hj1 : j + 1 ≤ n) :
    (HomologicalComplex.homologyMap (ξ.F.map (homOfLE hj1)) n).hom.comp
        (HomologicalComplex.homologyMap (incF ξ.F j) n).hom =
      (HomologicalComplex.homologyMap (ξ.F.map (homOfLE hj)) n).hom := by
  rw [show incF ξ.F j = ξ.F.map (homOfLE (Nat.le_succ j)) from rfl]
  rw [← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp,
    ← map_homOfLE_trans ξ.F (Nat.le_succ j) hj1]

/-- `jF` followed by the first differential is zero. -/
lemma jF_comp_d1' (ξ : Filtration C) (k t : ℕ) : jF ξ (k + 1) t ≫ d1 ξ k t = 0 := by
  have h : jF ξ (k + 1) t ≫ kF ξ k t = 0 :=
    ShortComplex.ShortExact.comp_δ (sesF_shortExact ξ k) ((k + 1) + t) (k + t)
      (by simp [ComplexShape.down]; omega)
  rw [d1, ← Category.assoc, h, zero_comp]

/-- The stratum `Ψ_{k+1}/Ψ_k` of the image filtration of `H_{k+1+t}(F_{k+1+t})` is finitely
generated whenever the `E²` term of bidegree `(k+1,t)` is. -/
theorem fgQuot_Psi_aux (ξ : Filtration C) (k t : ℕ) (ht : 1 ≤ t) (hE : E2quot ξ (k + 1) t) :
    FgQuot (Psi ξ ((k + 1) + t) k) (Psi ξ ((k + 1) + t) (k + 1)) := by
  have hkn : k ≤ (k + 1) + t := by omega
  have hk1n : k + 1 ≤ (k + 1) + t := by omega
  have hk2n : k + 2 ≤ (k + 1) + t := by omega
  -- the comparison maps `φ_j : H_n(F_j) → H_n(F_n)` and the inclusions `i_j`
  let φk : (ξ.F.obj k).homology ((k + 1) + t) →ₗ[ℤ]
      (ξ.F.obj ((k + 1) + t)).homology ((k + 1) + t) :=
    (HomologicalComplex.homologyMap (ξ.F.map (homOfLE hkn)) ((k + 1) + t)).hom
  let φk1 : (ξ.F.obj (k + 1)).homology ((k + 1) + t) →ₗ[ℤ]
      (ξ.F.obj ((k + 1) + t)).homology ((k + 1) + t) :=
    (HomologicalComplex.homologyMap (ξ.F.map (homOfLE hk1n)) ((k + 1) + t)).hom
  let φk2 : (ξ.F.obj (k + 2)).homology ((k + 1) + t) →ₗ[ℤ]
      (ξ.F.obj ((k + 1) + t)).homology ((k + 1) + t) :=
    (HomologicalComplex.homologyMap (ξ.F.map (homOfLE hk2n)) ((k + 1) + t)).hom
  let ik : (ξ.F.obj k).homology ((k + 1) + t) →ₗ[ℤ]
      (ξ.F.obj (k + 1)).homology ((k + 1) + t) :=
    (HomologicalComplex.homologyMap (incF ξ.F k) ((k + 1) + t)).hom
  let ik1 : (ξ.F.obj (k + 1)).homology ((k + 1) + t) →ₗ[ℤ]
      (ξ.F.obj (k + 2)).homology ((k + 1) + t) :=
    (HomologicalComplex.homologyMap (incF ξ.F (k + 1)) ((k + 1) + t)).hom
  let jF1 : (ξ.F.obj (k + 1)).homology ((k + 1) + t) →ₗ[ℤ] E1 ξ (k + 1) t :=
    (jF ξ (k + 1) t).hom
  let N : Submodule ℤ (E1 ξ (k + 1) t) := LinearMap.range (d1 ξ (k + 1) t).hom
  let M : Submodule ℤ (E1 ξ (k + 1) t) := LinearMap.ker (d1 ξ k t).hom
  -- fix the `ℤ`-module structure on the quotient so that it agrees with the one used by
  -- `Work.SSS.FgQuot`
  letI : Module ℤ (E1 ξ (k + 1) t ⧸ N) := Submodule.Quotient.module N
  let φ2 : (ξ.F.obj (k + 1)).homology ((k + 1) + t) →ₗ[ℤ] E1 ξ (k + 1) t ⧸ N :=
    (Submodule.mkQ N).comp jF1
  letI : Module ℤ ((ξ.F.obj ((k + 1) + t)).homology ((k + 1) + t) ⧸ Psi ξ ((k + 1) + t) k) :=
    Submodule.Quotient.module (Psi ξ ((k + 1) + t) k)
  let γ : (ξ.F.obj (k + 1)).homology ((k + 1) + t) →ₗ[ℤ]
      (ξ.F.obj ((k + 1) + t)).homology ((k + 1) + t) ⧸ Psi ξ ((k + 1) + t) k :=
    (Submodule.mkQ (Psi ξ ((k + 1) + t) k)).comp φk1
  have hφ2 : φ2 = (Submodule.mkQ N).comp jF1 := rfl
  have hγ : γ = (Submodule.mkQ (Psi ξ ((k + 1) + t) k)).comp φk1 := rfl
  have hcomp_k : φk1.comp ik = φk := homologyMap_incF_comp ξ ((k + 1) + t) k hkn hk1n
  have hcomp_k1 : φk2.comp ik1 = φk1 := homologyMap_incF_comp ξ ((k + 1) + t) (k + 1) hk1n hk2n
  have hφk : φk.range = Psi ξ ((k + 1) + t) k := (Psi_of_le ξ ((k + 1) + t) k hkn).symm
  have hφk1 : φk1.range = Psi ξ ((k + 1) + t) (k + 1) :=
    (Psi_of_le ξ ((k + 1) + t) (k + 1) hk1n).symm
  have hker_jF1 : jF1.ker = ik.range := ker_jF_eq_range_incF ξ k t
  have him_kF : (kF ξ (k + 1) t).hom.range = ik1.ker := range_kF_eq_ker_incF ξ (k + 1) t
  have hjF1_le_M : jF1.range ≤ M := by
    show (jF ξ (k + 1) t).hom.range ≤ (d1 ξ k t).hom.ker
    rw [LinearMap.range_le_ker_iff]
    have h := congrArg ModuleCat.Hom.hom (jF_comp_d1' ξ k t)
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero] using h
  -- the finiteness hypothesis, rewritten into the `FgQuot N M` form
  have hNM : FgQuot N M := by
    have h1 : (E1Complex ξ t).d ((k + 1) + 1) (k + 1) = d1 ξ (k + 1) t :=
      ChainComplex.of_d (fun s => E1 ξ s t) (fun s => d1 ξ s t) (k + 1)
    have h2 : (E1Complex ξ t).d (k + 1) ((k + 1) - 1) = d1 ξ k t :=
      ChainComplex.of_d (fun s => E1 ξ s t) (fun s => d1 ξ s t) k
    simp only [E2quot] at hE
    rw [h1, h2] at hE
    show FgQuot (LinearMap.range (d1 ξ (k + 1) t).hom) (LinearMap.ker (d1 ξ k t).hom)
    exact hE
  have hNM' : (M.map (Submodule.mkQ N)).FG := by simpa only [FgQuot] using hNM
  have hle : φ2.range ≤ M.map (Submodule.mkQ N) := by
    show ((Submodule.mkQ N).comp jF1).range ≤ M.map (Submodule.mkQ N)
    rw [LinearMap.range_comp]
    exact Submodule.map_mono hjF1_le_M
  have hrange : φ2.range.FG := Submodule.FG.of_le hNM' hle
  -- the kernel computation
  have hker : φ2.ker ≤ ⊥ ⊔ γ.ker := by
    intro x hx
    rw [bot_sup_eq]
    have hx0 : Submodule.mkQ N (jF1 x) = 0 := by
      simpa only [hφ2, LinearMap.comp_apply] using LinearMap.mem_ker.mp hx
    have hxN : jF1 x ∈ N := by
      have h := LinearMap.mem_ker.mpr hx0
      rwa [Submodule.ker_mkQ] at h
    obtain ⟨z, hz⟩ : ∃ z, (d1 ξ (k + 1) t).hom z = jF1 x := LinearMap.mem_range.mp hxN
    obtain ⟨y, hy, hyx⟩ : ∃ y ∈ (kF ξ (k + 1) t).hom.range, jF1 y = jF1 x :=
      ⟨(kF ξ (k + 1) t).hom z, LinearMap.mem_range.mpr ⟨z, rfl⟩, by
        rw [← hz, d1, ModuleCat.hom_comp, LinearMap.comp_apply]
        rfl⟩
    have hdiff : x - y ∈ ik.range := by
      have h1 : x - y ∈ jF1.ker := by
        rw [LinearMap.mem_ker, map_sub, hyx, sub_self]
      rwa [hker_jF1] at h1
    have hy0 : φk1 y = 0 := by
      have hiky : ik1 y = 0 := by
        have h := hy
        rw [him_kF, LinearMap.mem_ker] at h
        exact h
      rw [← hcomp_k1, LinearMap.comp_apply, hiky, map_zero]
    have hxd : φk1 (x - y) ∈ Psi ξ ((k + 1) + t) k := by
      have h1 : Submodule.map φk1 (LinearMap.range ik) = φk.range := by
        rw [← LinearMap.range_comp, hcomp_k]
      rw [← hφk, ← h1]
      exact Submodule.mem_map_of_mem hdiff
    have hzero : Submodule.mkQ (Psi ξ ((k + 1) + t) k) (φk1 (x - y)) = 0 := by
      have h := hxd
      rw [← Submodule.ker_mkQ (Psi ξ ((k + 1) + t) k), LinearMap.mem_ker] at h
      exact h
    have hxsum : φk1 x = φk1 (x - y) + φk1 y :=
      calc φk1 x = φk1 ((x - y) + y) := by rw [sub_add_cancel]
        _ = φk1 (x - y) + φk1 y := map_add φk1 (x - y) y
    have hfin : (Submodule.mkQ (Psi ξ ((k + 1) + t) k)) (φk1 x) = 0 := by
      rw [hxsum, LinearMap.map_add, hzero, hy0, map_zero, add_zero]
    show (Submodule.mkQ (Psi ξ ((k + 1) + t) k)) (φk1 x) = 0
    exact hfin
  have hgoal : γ.range.FG :=
    fg_range_of_ker_le γ φ2 ⊥ hker hrange (by rw [Submodule.map_bot]; exact Submodule.fg_bot)
  have hγrange : γ.range = (Psi ξ ((k + 1) + t) (k + 1)).map
      (Submodule.mkQ (Psi ξ ((k + 1) + t) k)) := by
    rw [hγ, LinearMap.range_comp, hφk1]
  simp only [FgQuot]
  rw [← hγrange]
  exact hgoal

theorem fgQuot_Psi {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Work.SSS.Filtration C) (m s : ℕ)
    (hs : 1 ≤ s) (hsm : s + 1 ≤ m) (hE : Work.SSS.E2quot ξ s (m - s)) :
    Work.SSS.FgQuot (Work.SSS.Psi ξ m (s - 1)) (Work.SSS.Psi ξ m s) := by
  have hk1 : s - 1 + 1 = s := by omega
  have ht : 1 ≤ m - s := by omega
  have hst : (s - 1 + 1) + (m - s) = m := by omega
  have h := fgQuot_Psi_aux ξ (s - 1) (m - s) ht (by simpa only [hk1] using hE)
  rwa [hst, hk1] at h

end Work.SSS.Lem
