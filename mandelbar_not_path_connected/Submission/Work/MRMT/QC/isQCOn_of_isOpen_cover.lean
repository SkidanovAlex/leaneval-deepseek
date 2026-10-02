/-
Work.MRMT — quasiconformality is a **local** notion: it glues over an open cover of `ℂ`.

The main result is

  `Work.MRMT.QC.isQCOn_of_isOpen_cover` :

if `f` is homeomorphic (on `ℂ`), quasiconformal on `U` with dilatation `μ` and quasiconformal
on `V` with the same dilatation `μ`, and `U ∪ V = ℂ` with `U`, `V` open, then `f` is
quasiconformal on `ℂ` with dilatation `μ`.

The proof decomposes the definition `Work.MRMT.IsQCOn`:

* openness and the homeomorphism clause are immediate;
* the a.e. bound `‖μ‖ ≤ k` glues with `k = max k₁ k₂`, and the pointwise Beltrami equation
  glues because every point of `ℂ` lies in `U` or in `V`;
* the Sobolev clause `Work.MRMT.HasW12LocOn f ℂ` is the substantive part:
  - `Work.MRMT.MemL2LocOn` glues over the cover (`memL2LocOn_of_isOpen_cover`),
    as it is tested on compact sets `K` and `K = (K ∩ U) ∪ (K ∩ V)`;
  - the weak Wirtinger derivatives on `ℂ` are taken to be the *pointwise* Wirtinger
    derivatives `dz f`, `dzbar f`:  on each of `U`, `V` these are weak derivatives because of
    the characterisation `hasW12LocOn_iff_dz`, and *the same function* `dz f` is then used on
    both pieces, so no gluing of two candidate derivatives (nor a.e. uniqueness on `U ∩ V`) is
    needed;
  - `isDzDerivOn_of_isOpen_cover` / `isDbarDerivOn_of_isOpen_cover` then upgrade the
    test-function identities from the members of the cover to `ℂ`: a test function `φ` is
    written `φ = χ₀ φ + χ₁ φ` with `tsupport (χᵢ φ) ⊆ U, V` by the smooth partition of unity
    `smooth_partition_of_unity_compact_cover` (`exists_testFunction_split`), and the defining
    integral identities for the two pieces are added.

Auxiliary API established here (all in namespace `Work.MRMT.QC`):
`hasW12LocOn_iff_dz` (the `W^{1,2}_{loc}` clause is equivalent to requiring the *pointwise*
Wirtinger derivatives to be weak derivatives), the a.e.-congruence lemmas
`MemL2LocOn.congr_ae`, `IsDzDerivOn.congr_ae`, `IsDbarDerivOn.congr_ae`, and the locality
lemmas `memL2LocOn_of_isOpen_cover`, `locallyIntegrableOn_of_isOpen_cover` — note that the
latter genuinely needs `U`, `V` open, since `LocallyIntegrableOn f U` only controls
integrability on neighbourhoods *within* `U`.
-/
import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.QC.smooth_partition_of_unity_compact_cover

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal

namespace Work.MRMT.QC

/-- `tsupport` of a real-valued function regarded as complex valued. -/
lemma tsupport_ofReal {χ : ℂ → ℝ} : tsupport (fun z => (χ z : ℂ)) = tsupport χ := by
  rw [tsupport, tsupport]
  congr 1
  ext z
  simp [Function.mem_support]

lemma support_ofReal {χ : ℂ → ℝ} : Function.support (fun z => (χ z : ℂ)) = Function.support χ := by
  ext z
  simp [Function.mem_support]

theorem dz_add_of_diff {F G : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) :
    Work.MRMT.dz (fun w => F w + G w) z = Work.MRMT.dz F z + Work.MRMT.dz G z := by
  have h := fderiv_add hF hG
  rw [Work.MRMT.dz, Work.MRMT.dz, Work.MRMT.dz,
    show fderiv ℝ (fun w : ℂ => F w + G w) z = fderiv ℝ F z + fderiv ℝ G z from h]
  simp only [add_apply]
  ring

theorem dzbar_add_of_diff {F G : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) :
    Work.MRMT.dzbar (fun w => F w + G w) z = Work.MRMT.dzbar F z + Work.MRMT.dzbar G z := by
  have h := fderiv_add hF hG
  rw [Work.MRMT.dzbar, Work.MRMT.dzbar, Work.MRMT.dzbar,
    show fderiv ℝ (fun w : ℂ => F w + G w) z = fderiv ℝ F z + fderiv ℝ G z from h]
  simp only [add_apply]
  ring

theorem memL2LocOn_of_isOpen_cover {f : ℂ → ℂ} {U V : Set ℂ}
    (hcov : U ∪ V = Set.univ) (h1 : Work.MRMT.MemL2LocOn f U) (h2 : Work.MRMT.MemL2LocOn f V) :
    Work.MRMT.MemL2LocOn f Set.univ := by
  intro K hK
  have hunion : (K ∩ U) ∪ (K ∩ V) = K := by
    rw [← Set.inter_union_distrib_left, hcov, Set.inter_univ]
  rw [Set.inter_univ, ← hunion]
  exact (h1 K hK).union (h2 K hK)

theorem locallyIntegrableOn_of_isOpen_cover {f : ℂ → ℂ} {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (h1 : LocallyIntegrableOn f U) (h2 : LocallyIntegrableOn f V) :
    LocallyIntegrableOn f Set.univ := by
  intro x _
  rw [nhdsWithin_univ]
  have hx : x ∈ U ∨ x ∈ V := by
    have : x ∈ U ∪ V := by rw [hcov]; trivial
    exact this
  rcases hx with hxU | hxV
  · obtain ⟨A, hA, hInt⟩ := h1 x hxU
    refine ⟨A, ?_, hInt⟩
    obtain ⟨W, hW, hWA⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hA
    exact mem_of_superset (Filter.inter_mem hW (hU.mem_nhds hxU)) (fun z hz => hWA ⟨hz.1, hz.2⟩)
  · obtain ⟨A, hA, hInt⟩ := h2 x hxV
    refine ⟨A, ?_, hInt⟩
    obtain ⟨W, hW, hWA⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hA
    exact mem_of_superset (Filter.inter_mem hW (hV.mem_nhds hxV)) (fun z hz => hWA ⟨hz.1, hz.2⟩)

theorem MemL2LocOn.congr_ae {f g : ℂ → ℂ} {U : Set ℂ} (h : Work.MRMT.MemL2LocOn f U)
    (hfg : f =ᵐ[volume] g) : Work.MRMT.MemL2LocOn g U := by
  intro K hK
  refine (h K hK).congr_fun_ae ?_
  filter_upwards [ae_restrict_of_ae hfg] with z hz
  simp [hz]

theorem IsDzDerivOn.congr_ae {f g h' : ℂ → ℂ} {U : Set ℂ} (H : Work.MRMT.IsDzDerivOn f g U)
    (hgh : g =ᵐ[volume] h') : Work.MRMT.IsDzDerivOn f h' U := by
  refine ⟨H.1, ?_, ?_⟩
  · intro x hx
    obtain ⟨A, hA, hInt⟩ := H.2.1 x hx
    exact ⟨A, hA, hInt.congr_fun_ae (by filter_upwards [ae_restrict_of_ae hgh] with z hz; exact hz)⟩
  · intro φ hφ
    obtain ⟨I1, I2, eq⟩ := H.2.2 φ hφ
    refine ⟨I1, I2.congr ?_, ?_⟩
    · filter_upwards [hgh] with z hz
      rw [hz]
    · have hae : (fun z => g z * (φ : ℂ → ℂ) z) =ᵐ[volume] (fun z => h' z * (φ : ℂ → ℂ) z) := by
        filter_upwards [hgh] with z hz
        rw [hz]
      rw [eq, integral_congr_ae hae]

theorem IsDbarDerivOn.congr_ae {f g h' : ℂ → ℂ} {U : Set ℂ} (H : Work.MRMT.IsDbarDerivOn f g U)
    (hgh : g =ᵐ[volume] h') : Work.MRMT.IsDbarDerivOn f h' U := by
  refine ⟨H.1, ?_, ?_⟩
  · intro x hx
    obtain ⟨A, hA, hInt⟩ := H.2.1 x hx
    exact ⟨A, hA, hInt.congr_fun_ae (by filter_upwards [ae_restrict_of_ae hgh] with z hz; exact hz)⟩
  · intro φ hφ
    obtain ⟨I1, I2, eq⟩ := H.2.2 φ hφ
    refine ⟨I1, I2.congr ?_, ?_⟩
    · filter_upwards [hgh] with z hz
      rw [hz]
    · have hae : (fun z => g z * (φ : ℂ → ℂ) z) =ᵐ[volume] (fun z => h' z * (φ : ℂ → ℂ) z) := by
        filter_upwards [hgh] with z hz
        rw [hz]
      rw [eq, integral_congr_ae hae]

theorem hasW12LocOn_iff_dz {g : ℂ → ℂ} {U : Set ℂ} :
    Work.MRMT.HasW12LocOn g U ↔
      Work.MRMT.MemL2LocOn g U ∧ Work.MRMT.MemL2LocOn (Work.MRMT.dz g) U ∧
        Work.MRMT.MemL2LocOn (Work.MRMT.dzbar g) U ∧
        Work.MRMT.IsDzDerivOn g (Work.MRMT.dz g) U ∧
        Work.MRMT.IsDbarDerivOn g (Work.MRMT.dzbar g) U := by
  constructor
  · rintro ⟨hmem, gz, gzbar, hdz, hdbar, hmgz, hmgzbar, heqz, heqzbar⟩
    exact ⟨hmem, MemL2LocOn.congr_ae hmgz heqz, MemL2LocOn.congr_ae hmgzbar heqzbar,
      IsDzDerivOn.congr_ae hdz heqz, IsDbarDerivOn.congr_ae hdbar heqzbar⟩
  · rintro ⟨hmem, hz, hbar, hdz, hdbar⟩
    exact ⟨hmem, Work.MRMT.dz g, Work.MRMT.dzbar g, hdz, hdbar, hz, hbar,
      EventuallyEq.refl _ _, EventuallyEq.refl _ _⟩

/-- Smooth partition of unity, packaged for a two-set open cover: a test function `φ` splits as
`φ = φ₁ + φ₂` with `tsupport φ₁ ⊆ U` and `tsupport φ₂ ⊆ V`. -/
theorem exists_testFunction_split {U V : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (φ : 𝓓(⊤, ℂ)) :
    ∃ φ₁ φ₂ : 𝓓(⊤, ℂ), tsupport (φ₁ : ℂ → ℂ) ⊆ U ∧ tsupport (φ₂ : ℂ → ℂ) ⊆ V ∧
      (∀ z, (φ : ℂ → ℂ) z = (φ₁ : ℂ → ℂ) z + (φ₂ : ℂ → ℂ) z) ∧
      (∀ z, DifferentiableAt ℝ (φ₁ : ℂ → ℂ) z) ∧ (∀ z, DifferentiableAt ℝ (φ₂ : ℂ → ℂ) z) := by
  classical
  have hKc : IsCompact (tsupport (φ : ℂ → ℂ)) := φ.hasCompactSupport.isCompact
  have hKcov : tsupport (φ : ℂ → ℂ) ⊆ ⋃ i : Fin 2, (![U, V] : Fin 2 → Set ℂ) i := by
    intro z hz
    have hz' : z ∈ U ∨ z ∈ V := by
      have : z ∈ U ∪ V := by rw [hcov]; trivial
      exact this
    rcases hz' with h | h
    · exact Set.mem_iUnion.mpr ⟨0, by simpa using h⟩
    · exact Set.mem_iUnion.mpr ⟨1, by simpa using h⟩
  obtain ⟨χ, hχdiff, hχcs, hχts, hχnonneg, W, hWopen, hKW, hWV, hχsum⟩ :=
    smooth_partition_of_unity_compact_cover hKc (fun i : Fin 2 => (![U, V] : Fin 2 → Set ℂ) i)
      (fun i => by fin_cases i <;> simpa) hKcov
  have hχts0 : tsupport (χ 0) ⊆ U := by simpa using hχts 0
  have hχts1 : tsupport (χ 1) ⊆ V := by simpa using hχts 1
  have hcd0 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z => (χ 0 z : ℂ) * (φ : ℂ → ℂ) z) :=
    ((Complex.ofRealCLM.contDiff).comp (hχdiff 0)).mul φ.contDiff
  have hcd1 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z => (χ 1 z : ℂ) * (φ : ℂ → ℂ) z) :=
    ((Complex.ofRealCLM.contDiff).comp (hχdiff 1)).mul φ.contDiff
  have hcs0 : HasCompactSupport (fun z => (χ 0 z : ℂ) * (φ : ℂ → ℂ) z) :=
    HasCompactSupport.of_support_subset_isCompact (hχcs 0).isCompact
      ((support_mul_subset_left (fun z => (χ 0 z : ℂ)) (φ : ℂ → ℂ)).trans (by rw [support_ofReal]; exact subset_closure))
  have hcs1 : HasCompactSupport (fun z => (χ 1 z : ℂ) * (φ : ℂ → ℂ) z) :=
    HasCompactSupport.of_support_subset_isCompact (hχcs 1).isCompact
      ((support_mul_subset_left (fun z => (χ 1 z : ℂ)) (φ : ℂ → ℂ)).trans (by rw [support_ofReal]; exact subset_closure))
  have hts0 : tsupport (fun z => (χ 0 z : ℂ) * (φ : ℂ → ℂ) z) ⊆ U :=
    (tsupport_mul_subset_left (f := fun z => (χ 0 z : ℂ)) (g := (φ : ℂ → ℂ))).trans <| by
      rw [tsupport_ofReal]; exact hχts0
  have hts1 : tsupport (fun z => (χ 1 z : ℂ) * (φ : ℂ → ℂ) z) ⊆ V :=
    (tsupport_mul_subset_left (f := fun z => (χ 1 z : ℂ)) (g := (φ : ℂ → ℂ))).trans <| by
      rw [tsupport_ofReal]; exact hχts1
  refine ⟨⟨fun z => (χ 0 z : ℂ) * (φ : ℂ → ℂ) z, hcd0, hcs0, fun _ _ => trivial⟩,
    ⟨fun z => (χ 1 z : ℂ) * (φ : ℂ → ℂ) z, hcd1, hcs1, fun _ _ => trivial⟩, hts0, hts1, ?_, ?_, ?_⟩
  · intro z
    change (φ : ℂ → ℂ) z = (χ 0 z : ℂ) * (φ : ℂ → ℂ) z + (χ 1 z : ℂ) * (φ : ℂ → ℂ) z
    by_cases hz : z ∈ tsupport (φ : ℂ → ℂ)
    · have hzW : z ∈ W := hKW hz
      have hsum1 : χ 0 z + χ 1 z = 1 := by
        have h := hχsum z hzW
        rwa [Fin.sum_univ_two] at h
      rw [← add_mul, ← Complex.ofReal_add, hsum1, Complex.ofReal_one, one_mul]
    · have hz0 : (φ : ℂ → ℂ) z = 0 := image_eq_zero_of_notMem_tsupport hz
      rw [hz0]; ring
  · intro z
    exact ((hcd0.differentiable (by simp)).differentiableAt)
  · intro z
    exact ((hcd1.differentiable (by simp)).differentiableAt)

theorem isDzDerivOn_of_isOpen_cover {f g : ℂ → ℂ} {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (h1 : Work.MRMT.IsDzDerivOn f g U) (h2 : Work.MRMT.IsDzDerivOn f g V) :
    Work.MRMT.IsDzDerivOn f g Set.univ := by
  refine ⟨locallyIntegrableOn_of_isOpen_cover hU hV hcov h1.1 h2.1,
    locallyIntegrableOn_of_isOpen_cover hU hV hcov h1.2.1 h2.2.1, ?_⟩
  intro φ hφ
  obtain ⟨φ₁, φ₂, hts₁, hts₂, hsum, hd₁, hd₂⟩ := exists_testFunction_split hU hV hcov φ
  obtain ⟨I₁a, I₁b, eq₁⟩ := h1.2.2 φ₁ hts₁
  obtain ⟨I₂a, I₂b, eq₂⟩ := h2.2.2 φ₂ hts₂
  have hd : ∀ z, Work.MRMT.dz (φ : ℂ → ℂ) z =
      Work.MRMT.dz (φ₁ : ℂ → ℂ) z + Work.MRMT.dz (φ₂ : ℂ → ℂ) z := by
    intro z
    rw [show (φ : ℂ → ℂ) = fun w => (φ₁ : ℂ → ℂ) w + (φ₂ : ℂ → ℂ) w from funext hsum]
    exact dz_add_of_diff (hd₁ z) (hd₂ z)
  have hInt1 : Integrable (fun z => f z * Work.MRMT.dz (φ : ℂ → ℂ) z) := by
    refine (I₁a.add I₂a).congr ?_
    filter_upwards with z
    change f z * Work.MRMT.dz (φ₁ : ℂ → ℂ) z + f z * Work.MRMT.dz (φ₂ : ℂ → ℂ) z = f z * Work.MRMT.dz (φ : ℂ → ℂ) z
    rw [hd z]; ring
  have hInt2 : Integrable (fun z => g z * (φ : ℂ → ℂ) z) := by
    refine (I₁b.add I₂b).congr ?_
    filter_upwards with z
    change g z * (φ₁ : ℂ → ℂ) z + g z * (φ₂ : ℂ → ℂ) z = g z * (φ : ℂ → ℂ) z
    rw [hsum z]; ring
  refine ⟨hInt1, hInt2, ?_⟩
  have s1 : (∫ z, f z * Work.MRMT.dz (φ : ℂ → ℂ) z)
      = ∫ z, (f z * Work.MRMT.dz (φ₁ : ℂ → ℂ) z + f z * Work.MRMT.dz (φ₂ : ℂ → ℂ) z) :=
    integral_congr_ae (Eventually.of_forall (fun z => by simp only [hd z]; ring))
  have s2 : (∫ z, (f z * Work.MRMT.dz (φ₁ : ℂ → ℂ) z + f z * Work.MRMT.dz (φ₂ : ℂ → ℂ) z))
      = (∫ z, f z * Work.MRMT.dz (φ₁ : ℂ → ℂ) z)
        + (∫ z, f z * Work.MRMT.dz (φ₂ : ℂ → ℂ) z) :=
    integral_add I₁a I₂a
  have s3 : (∫ z, f z * Work.MRMT.dz (φ₁ : ℂ → ℂ) z)
        + (∫ z, f z * Work.MRMT.dz (φ₂ : ℂ → ℂ) z)
      = (-∫ z, g z * (φ₁ : ℂ → ℂ) z) + (-∫ z, g z * (φ₂ : ℂ → ℂ) z) :=
    congrArg₂ (fun a b : ℂ => a + b) eq₁ eq₂
  have s4 : (-∫ z, g z * (φ₁ : ℂ → ℂ) z) + (-∫ z, g z * (φ₂ : ℂ → ℂ) z)
      = -((∫ z, g z * (φ₁ : ℂ → ℂ) z) + (∫ z, g z * (φ₂ : ℂ → ℂ) z)) :=
    (neg_add _ _).symm
  have s5 : (∫ z, g z * (φ₁ : ℂ → ℂ) z) + (∫ z, g z * (φ₂ : ℂ → ℂ) z)
      = (∫ z, g z * (φ : ℂ → ℂ) z) :=
    (integral_add I₁b I₂b).symm.trans
      (integral_congr_ae (Eventually.of_forall (fun z => by simp only [hsum z]; ring)))
  exact s1.trans (s2.trans (s3.trans (s4.trans (congrArg Neg.neg s5))))

theorem isDbarDerivOn_of_isOpen_cover {f g : ℂ → ℂ} {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (h1 : Work.MRMT.IsDbarDerivOn f g U) (h2 : Work.MRMT.IsDbarDerivOn f g V) :
    Work.MRMT.IsDbarDerivOn f g Set.univ := by
  refine ⟨locallyIntegrableOn_of_isOpen_cover hU hV hcov h1.1 h2.1,
    locallyIntegrableOn_of_isOpen_cover hU hV hcov h1.2.1 h2.2.1, ?_⟩
  intro φ hφ
  obtain ⟨φ₁, φ₂, hts₁, hts₂, hsum, hd₁, hd₂⟩ := exists_testFunction_split hU hV hcov φ
  obtain ⟨I₁a, I₁b, eq₁⟩ := h1.2.2 φ₁ hts₁
  obtain ⟨I₂a, I₂b, eq₂⟩ := h2.2.2 φ₂ hts₂
  have hd : ∀ z, Work.MRMT.dzbar (φ : ℂ → ℂ) z =
      Work.MRMT.dzbar (φ₁ : ℂ → ℂ) z + Work.MRMT.dzbar (φ₂ : ℂ → ℂ) z := by
    intro z
    rw [show (φ : ℂ → ℂ) = fun w => (φ₁ : ℂ → ℂ) w + (φ₂ : ℂ → ℂ) w from funext hsum]
    exact dzbar_add_of_diff (hd₁ z) (hd₂ z)
  have hInt1 : Integrable (fun z => f z * Work.MRMT.dzbar (φ : ℂ → ℂ) z) := by
    refine (I₁a.add I₂a).congr ?_
    filter_upwards with z
    change f z * Work.MRMT.dzbar (φ₁ : ℂ → ℂ) z + f z * Work.MRMT.dzbar (φ₂ : ℂ → ℂ) z = f z * Work.MRMT.dzbar (φ : ℂ → ℂ) z
    rw [hd z]; ring
  have hInt2 : Integrable (fun z => g z * (φ : ℂ → ℂ) z) := by
    refine (I₁b.add I₂b).congr ?_
    filter_upwards with z
    change g z * (φ₁ : ℂ → ℂ) z + g z * (φ₂ : ℂ → ℂ) z = g z * (φ : ℂ → ℂ) z
    rw [hsum z]; ring
  refine ⟨hInt1, hInt2, ?_⟩
  have s1 : (∫ z, f z * Work.MRMT.dzbar (φ : ℂ → ℂ) z)
      = ∫ z, (f z * Work.MRMT.dzbar (φ₁ : ℂ → ℂ) z + f z * Work.MRMT.dzbar (φ₂ : ℂ → ℂ) z) :=
    integral_congr_ae (Eventually.of_forall (fun z => by simp only [hd z]; ring))
  have s2 : (∫ z, (f z * Work.MRMT.dzbar (φ₁ : ℂ → ℂ) z + f z * Work.MRMT.dzbar (φ₂ : ℂ → ℂ) z))
      = (∫ z, f z * Work.MRMT.dzbar (φ₁ : ℂ → ℂ) z)
        + (∫ z, f z * Work.MRMT.dzbar (φ₂ : ℂ → ℂ) z) :=
    integral_add I₁a I₂a
  have s3 : (∫ z, f z * Work.MRMT.dzbar (φ₁ : ℂ → ℂ) z)
        + (∫ z, f z * Work.MRMT.dzbar (φ₂ : ℂ → ℂ) z)
      = (-∫ z, g z * (φ₁ : ℂ → ℂ) z) + (-∫ z, g z * (φ₂ : ℂ → ℂ) z) :=
    congrArg₂ (fun a b : ℂ => a + b) eq₁ eq₂
  have s4 : (-∫ z, g z * (φ₁ : ℂ → ℂ) z) + (-∫ z, g z * (φ₂ : ℂ → ℂ) z)
      = -((∫ z, g z * (φ₁ : ℂ → ℂ) z) + (∫ z, g z * (φ₂ : ℂ → ℂ) z)) :=
    (neg_add _ _).symm
  have s5 : (∫ z, g z * (φ₁ : ℂ → ℂ) z) + (∫ z, g z * (φ₂ : ℂ → ℂ) z)
      = (∫ z, g z * (φ : ℂ → ℂ) z) :=
    (integral_add I₁b I₂b).symm.trans
      (integral_congr_ae (Eventually.of_forall (fun z => by simp only [hsum z]; ring)))
  exact s1.trans (s2.trans (s3.trans (s4.trans (congrArg Neg.neg s5))))

theorem hasW12LocOn_of_isOpen_cover {g : ℂ → ℂ} {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (h1 : Work.MRMT.HasW12LocOn g U) (h2 : Work.MRMT.HasW12LocOn g V) :
    Work.MRMT.HasW12LocOn g Set.univ := by
  obtain ⟨hm1, hz1, hb1, hdz1, hdb1⟩ := hasW12LocOn_iff_dz.mp h1
  obtain ⟨hm2, hz2, hb2, hdz2, hdb2⟩ := hasW12LocOn_iff_dz.mp h2
  refine hasW12LocOn_iff_dz.mpr ⟨memL2LocOn_of_isOpen_cover hcov hm1 hm2,
    memL2LocOn_of_isOpen_cover hcov hz1 hz2, memL2LocOn_of_isOpen_cover hcov hb1 hb2, ?_, ?_⟩
  · exact isDzDerivOn_of_isOpen_cover hU hV hcov hdz1 hdz2
  · exact isDbarDerivOn_of_isOpen_cover hU hV hcov hdb1 hdb2

theorem isQCOn_of_isOpen_cover {f : ℂ → ℂ} {μ : ℂ → ℂ} {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (hhom : Work.MRMT.IsHomeomorphOn f Set.univ)
    (h1 : Work.MRMT.IsQCOn f U μ) (h2 : Work.MRMT.IsQCOn f V μ) :
    Work.MRMT.IsQCOn f Set.univ μ := by
  obtain ⟨k1, hk1, hb1⟩ := h1.2.2.2.1
  obtain ⟨k2, hk2, hb2⟩ := h2.2.2.2.1
  refine ⟨isOpen_univ, hhom, hasW12LocOn_of_isOpen_cover hU hV hcov h1.2.2.1 h2.2.2.1,
    ⟨max k1 k2, max_lt hk1 hk2, ?_⟩, ?_⟩
  · filter_upwards [hb1, hb2] with z hz1 hz2
    intro _
    have hz : z ∈ U ∨ z ∈ V := by
      have : z ∈ U ∪ V := by rw [hcov]; trivial
      exact this
    rcases hz with h | h
    · exact le_trans (hz1 h) (le_max_left _ _)
    · exact le_trans (hz2 h) (le_max_right _ _)
  · filter_upwards [h1.2.2.2.2, h2.2.2.2.2] with z hz1 hz2
    intro _
    have hz : z ∈ U ∨ z ∈ V := by
      have : z ∈ U ∪ V := by rw [hcov]; trivial
      exact this
    rcases hz with h | h
    · exact hz1 h
    · exact hz2 h

end Work.MRMT.QC
