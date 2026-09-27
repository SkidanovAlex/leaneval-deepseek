import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.gapA.geodFacts
import Submission.Work.Mostow.gapA.mem_geodSet_iff_span
import Submission.Work.Mostow.gapA.rotSetup
import Submission.Work.Mostow.gapA.rotationFormula
import Submission.Work.Mostow.gapA.rotAux
import Submission.Work.Mostow.gapA.nearId_isOriented
import Submission.Work.Mostow.gapA.axis_fixeset
import Submission.Work.Mostow.gapA.oriented_generator
import Submission.Work.Mostow.gapA.order_mul_sin_of_cos
import Submission.Work.Mostow.gapA.axisPB
import Submission.Work.Mostow.gapA.ogAux
import Submission.Work.Mostow.gapA.depthPlus3
import Submission.Work.Mostow.finite_nearStab

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open Work.Mostow
open Matrix

noncomputable section

/-- The pointwise stabiliser of the geodesic `geodSet a b` inside `Γ` is finite. -/
lemma finite_stab (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO 3 1))
    (hdisc : IsDiscrete (SetLike.coe Γ)) (a b : Submission.Mostow.E 3)
    (u₀ : Submission.Mostow.E 3) (hu₀ : u₀ ∈ Work.Mostow.geodSet a b) :
    {g : LeanEval.Geometry.MostowRigidity.PO 3 1 |
      g ∈ Γ ∧ ∀ u : Submission.Mostow.E 3, u ∈ Work.Mostow.geodSet a b → g • u = u}.Finite := by
  have hpb : POBasic 3 := POBasic.ofProp hA
  have hid : HypIsoData 3 := HypIsoData.ofProp hI
  have hsub : {g : LeanEval.Geometry.MostowRigidity.PO 3 1 |
        g ∈ Γ ∧ ∀ u : Submission.Mostow.E 3, u ∈ Work.Mostow.geodSet a b → g • u = u}
      ⊆ {g : LeanEval.Geometry.MostowRigidity.PO 3 1 |
          g ∈ Γ ∧ hdist (0 : Submission.Mostow.E 3) (g • (0 : Submission.Mostow.E 3))
            ≤ 2 * hdist (0 : Submission.Mostow.E 3) u₀} := by
    rintro g ⟨hgΓ, hgfix⟩
    refine ⟨hgΓ, ?_⟩
    have h1 := hid.triangle (0 : Submission.Mostow.E 3) u₀ (g • (0 : Submission.Mostow.E 3))
    have h2 : hdist u₀ (g • (0 : Submission.Mostow.E 3))
        = hdist (g • u₀) (g • (0 : Submission.Mostow.E 3)) := by rw [hgfix u₀ hu₀]
    rw [h2, hid.isom_smul, hid.symm u₀ 0] at h1
    linarith
  have hfinite := finite_nearStab hpb hid hdisc (2 * hdist (0 : Submission.Mostow.E 3) u₀)
  have h2 : {g : LeanEval.Geometry.MostowRigidity.PO 3 1 |
        g ∈ Γ ∧ hdist (0 : Submission.Mostow.E 3) (g • (0 : Submission.Mostow.E 3))
          ≤ 2 * hdist (0 : Submission.Mostow.E 3) u₀}.Finite := by
    have himg := hfinite.image (fun γ : Γ => (γ : LeanEval.Geometry.MostowRigidity.PO 3 1))
    convert himg using 1
    ext g
    constructor
    · rintro ⟨hgΓ, hg⟩
      exact ⟨⟨g, hgΓ⟩, hg, rfl⟩
    · rintro ⟨γ, hγ, hgd⟩
      rw [← hgd]
      exact ⟨γ.2, hγ⟩
  exact h2.subset hsub

/-- `x ^ k = x ^ (k % N).toNat` when `x ^ N = 1`. -/
lemma zpow_eq_pow_emod {G : Type*} [Group G] (x : G) {N : ℕ} (hN : 0 < N) (hx : x ^ N = 1)
    (k : ℤ) : x ^ k = x ^ ((k % (N : ℤ)).toNat) := by
  have hNne : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNk : (N : ℤ) ∣ (((k % (N : ℤ)).toNat : ℤ) - k) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg k hNne)]
    have h := Int.emod_add_mul_ediv k (N : ℤ)
    exact ⟨-(k / (N : ℤ)), by linarith⟩
  have hdvd : (orderOf x : ℤ) ∣ (((k % (N : ℤ)).toNat : ℤ) - k) :=
    dvd_trans (by exact_mod_cast orderOf_dvd_iff_pow_eq_one.mpr hx) hNk
  rw [← zpow_natCast x ((k % (N : ℤ)).toNat), zpow_eq_zpow_iff_modEq]
  exact Int.modEq_iff_dvd.mpr hdvd


/-- **The rotation gap from the normal-plane pairing.**  For an orientation preserving isometry
`f` of finite order which fixes the geodesic `geodSet a b` pointwise and whose action on the
normal plane has constant pairing `c ≠ 1`, the rotation angle `arccos c` satisfies
`2 ≤ orderOf f · sin (arccos c / 2)`.

The proof uses the complex parameter `zOf B f ∈ ℂˣ` of the normal action (`ogAux`): it is a root
of unity of order dividing `orderOf f`, and its real part is `c`, so `c = cos (2πn/N)` for some
`n : ℤ`; the numerical lemma `order_mul_sin_of_cos` then gives the bound. -/
lemma orderBound_of_pairing
    (hA : Submission.Mostow.POActionProp 3) (hI : Submission.Mostow.HypIsometryProp 3)
    (f : LeanEval.Geometry.MostowRigidity.PO 3 1) (a b : Submission.Mostow.E 3)
    (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3) (hab : a ≠ b)
    (c : ℝ) (hcne : c ≠ 1)
    (hparam : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Work.Mostow.mink Z (Work.Mostow.nvec a) = 0 →
      Work.Mostow.mink Z (Work.Mostow.nvec b) = 0 →
      Work.Mostow.mink (Matrix.mulVec (Work.Mostow.emat f) Z) Z = c * Work.Mostow.mink Z Z)
    (hfin : IsOfFinOrder f) (hor : Work.Mostow.IsOriented f)
    (hax : ∀ u : Submission.Mostow.E 3, u ∈ Work.Mostow.geodSet a b → f • u = u) :
    2 ≤ (orderOf f : ℝ) * Real.sin (Real.arccos c / 2) := by
  classical
  obtain ⟨B⟩ := exists_PB ha hb hab
  have hfam : f ∈ AxisSub hA a b := mem_AxisSub_of_isOriented_of_fixes hA hI ha hb hab hor hax
  have hdet : (rotMat B f).det = 1 := rotMat_det hA ha hb hab B f hfam
  obtain ⟨h01, h11, -⟩ := rotMat_form hA B hfam hdet
  have hform : rotMat B f = !![rot00 B f, -rot10 B f; rot10 B f, rot00 B f] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h11]
  have hc : c = rot00 B f := by
    have h1 := hparam B.e1 (mem_NormP.mp B.mem1).1 (mem_NormP.mp B.mem1).2
    have h2 := mink_mulVec_zOf hA B hfam hform B.mem1
    rw [B.n11, mul_one] at h1 h2
    linarith
  have hNpos : 0 < orderOf f := orderOf_pos_iff.mpr hfin
  have hNposR : (0:ℝ) < (orderOf f : ℝ) := by exact_mod_cast hNpos
  have hζpow : (zOf B f) ^ (orderOf f) = 1 := by
    rw [← zOf_pow hA B hfam hform (orderOf f), pow_orderOf_eq_one f]
    apply Complex.ext
    · simp [zOf, rot00, rot10, emat_one hA, B.n11]
    · simp [zOf, rot00, rot10, emat_one hA, B.n12]
  have hζne : zOf B f ≠ 0 := zOf_ne_zero hA B hfam
  set w : ℂ := Complex.log (zOf B f) with hwdef
  have hwexp : Complex.exp w = zOf B f := by
    rw [hwdef]; exact Complex.exp_log hζne
  have hexp1 : Complex.exp ((orderOf f : ℂ) * w) = 1 := by
    rw [Complex.exp_nat_mul, hwexp, hζpow]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp1
  rw [← Complex.ofReal_natCast (orderOf f)] at hn
  have hM : (↑n : ℂ) * (2 * ↑Real.pi * Complex.I)
      = ((2 * Real.pi * (n:ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hM] at hn
  have hre : (orderOf f : ℝ) * w.re = 0 := by
    have h := congrArg Complex.re hn
    simpa [Complex.mul_re] using h
  have him : (orderOf f : ℝ) * w.im = 2 * Real.pi * (n:ℝ) := by
    have h := congrArg Complex.im hn
    simpa [Complex.mul_im] using h
  have hwre : w.re = 0 := by
    rcases mul_eq_zero.mp hre with h | h
    · exact absurd h (ne_of_gt hNposR)
    · exact h
  have hwim : w.im = 2 * Real.pi * (n:ℝ) / (orderOf f : ℝ) := by
    rw [eq_div_iff (ne_of_gt hNposR)]
    linarith [him]
  have hζre : c = Real.cos (2 * Real.pi * (n:ℝ) / (orderOf f : ℝ)) := by
    have h1 : c = (Complex.exp w).re := by rw [hc, ← zOf_re, ← hwexp]
    rw [h1, Complex.exp_re, hwre]
    simp [hwim]
  have hnum := order_mul_sin_of_cos (orderOf f) hNpos
    (2 * Real.pi * (n:ℝ) / (orderOf f : ℝ))
    ⟨n, by field_simp⟩ (by rw [← hζre]; exact hcne)
  simpa [← hζre] using hnum

theorem rotData3 (hA : Submission.Mostow.POActionProp 3) (hI : Submission.Mostow.HypIsometryProp 3)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO 3 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (f : LeanEval.Geometry.MostowRigidity.PO 3 1) (hf : f ≠ 1) (hfin : IsOfFinOrder f) (hfmem : f ∈ Γ)
    (z : Submission.Mostow.E 3) (η : ℝ) (hη : 0 < η) (hη2 : η ≤ 1)
    (hnear : Submission.Mostow.NearIdAt f z η) :
    ∃ (a b : Submission.Mostow.E 3) (θ : ℝ) (M : ℕ) (b₀ : LeanEval.Geometry.MostowRigidity.PO 3 1),
      a ∈ Submission.Mostow.Sph 3 ∧ b ∈ Submission.Mostow.Sph 3 ∧ a ≠ b ∧ 0 < θ ∧ θ ≤ Real.pi ∧
      Work.Mostow.IsRotationAbout f a b θ ∧ 2 ≤ (orderOf f : ℝ) * Real.sin (θ / 2) ∧
      0 < M ∧ b₀ ∈ Γ ∧ orderOf b₀ = M ∧ Work.Mostow.IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)) ∧
      (∀ g : LeanEval.Geometry.MostowRigidity.PO 3 1, g ∈ Γ →
        (∀ u : Submission.Mostow.E 3, u ∈ Work.Mostow.geodSet a b → g • u = u) →
        (∃ k : ℤ, g = b₀ ^ k) ∨ ¬ Work.Mostow.IsOriented g) ∧
      (∃ k : ℤ, f = b₀ ^ k) ∧
      Real.sinh (Work.Mostow.distGeod a b z) * Real.sin (Real.pi / (M : ℝ)) ≤ η / 2 := by
  have hor : Work.Mostow.IsOriented f := nearId_isOriented hA hI f z η hη hη2 hnear
  obtain ⟨a, b, ha, hb, hab, hfix⟩ := axis_fixeset hA hI f hf hfin hor
  have hax : ∀ u : Submission.Mostow.E 3, u ∈ Work.Mostow.geodSet a b → f • u = u :=
    fun u hu => (hfix u).mpr hu
  obtain ⟨b₀, hb0Γ, horb0, hb0fin, hfixb0, hfk, hgen, hpar⟩ :=
    oriented_generator hA hI Γ hΓ a b ha hb hab f hfmem hf hfin hor hax
  -- the exponent reduced modulo `M`
  obtain ⟨k, hkff⟩ := hfk
  have hMpos : 0 < orderOf b₀ := orderOf_pos_iff.mpr hb0fin
  set M : ℕ := orderOf b₀ with hMdef
  have hb0ne : b₀ ≠ 1 := by
    intro h
    exact hf (by rw [hkff, h]; simp)
  have hM2 : 2 ≤ M := by
    rw [hMdef]
    rcases lt_or_eq_of_le (Nat.one_le_iff_ne_zero.mpr hMpos.ne') with h' | h'
    · exact h'
    · exact absurd (orderOf_eq_one_iff.mp (hMdef.symm.trans h'.symm)) hb0ne
  have hb0pow : b₀ ^ M = 1 := by rw [hMdef]; exact pow_orderOf_eq_one b₀
  set m : ℕ := (k % (M : ℤ)).toNat with hmdef
  have hmk : f = b₀ ^ m := by rw [hkff, hmdef]; exact zpow_eq_pow_emod b₀ hMpos hb0pow k
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      rw [h, pow_zero] at hmk
      exact hf hmk
    · exact h
  have hmlt : m < M := by
    have h1 : (k % (M : ℤ)) < M := Int.emod_lt_of_pos k (by exact_mod_cast hMpos)
    have h2 : 0 ≤ k % (M : ℤ) := Int.emod_nonneg k (by exact_mod_cast hMpos.ne')
    rw [hmdef]
    omega
  -- the parameter of `emat f`
  have hcf : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, mink Z (nvec a) = 0 → mink Z (nvec b) = 0 →
      mink (Matrix.mulVec (emat f) Z) Z
        = Real.cos (2 * Real.pi * (m : ℝ) / (M : ℝ)) * mink Z Z := by
    intro Z hZ1 hZ2
    rw [hmk, emat_pow hA, hpar m Z hZ1 hZ2]
  -- the angle
  set θ : ℝ := Real.arccos (Real.cos (2 * Real.pi * (m : ℝ) / (M : ℝ))) with hθdef
  have hcabs : |Real.cos (2 * Real.pi * (m : ℝ) / (M : ℝ))| ≤ 1 := Real.abs_cos_le_one _
  have hcne : Real.cos (2 * Real.pi * (m : ℝ) / (M : ℝ)) ≠ 1 := by
    intro h
    have h2 : Real.sin (2 * Real.pi * (m : ℝ) / (M : ℝ)) = 0 := by
      have hh := Real.sin_sq_add_cos_sq (2 * Real.pi * (m : ℝ) / (M : ℝ))
      rw [h] at hh
      nlinarith [sq_nonneg (Real.sin (2 * Real.pi * (m : ℝ) / (M : ℝ)))]
    obtain ⟨j, hj⟩ := Real.sin_eq_zero_iff.mp h2
    have hMne : (M : ℝ) ≠ 0 := by positivity
    have h3 : 2 * (m : ℝ) = (j : ℝ) * (M : ℝ) := by
      field_simp at hj
      linarith [hj]
    have h3' : (2 * (m : ℤ)) = j * (M : ℤ) := by exact_mod_cast h3
    have h4 : (M : ℤ) ∣ (2 * (m : ℤ)) := ⟨j, by rw [h3']; ring⟩
    have h5 : M ∣ 2 * m := by exact_mod_cast h4
    have h8 : 2 * m = M := by
      obtain ⟨t, ht⟩ := h5
      have ht1 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h0 | h0
        · rw [h0, mul_zero] at ht; omega
        · exact h0
      have ht2 : t ≤ 1 := by
        by_contra hh
        push_neg at hh
        have h2 : 2 * M ≤ M * t := by
          calc 2 * M = M * 2 := by ring
            _ ≤ M * t := Nat.mul_le_mul_left M hh
        omega
      have ht3 : t = 1 := by omega
      rw [ht3, mul_one] at ht
      omega
    have h9 : Real.cos (2 * Real.pi * (m : ℝ) / (M : ℝ)) = -1 := by
      have hpi : 2 * Real.pi * (m : ℝ) / (M : ℝ) = Real.pi := by
        have hM' : (M : ℝ) = 2 * (m : ℝ) := by rw [← h8]; push_cast; ring
        rw [hM']
        field_simp
      rw [hpi, Real.cos_pi]
    rw [h9] at h
    norm_num at h
  have hθ0 : 0 < θ := by
    rw [hθdef, Real.arccos_pos]
    exact lt_of_le_of_ne (abs_le.mp hcabs).2 hcne
  have hθπ : θ ≤ Real.pi := by
    rw [hθdef]; exact Real.arccos_le_pi _
  have hθcos : Real.cos θ = Real.cos (2 * Real.pi * (m : ℝ) / (M : ℝ)) := by
    rw [hθdef]
    exact Real.cos_arccos (abs_le.mp hcabs).1 (abs_le.mp hcabs).2
  have hrotf : Work.Mostow.IsRotationAbout f a b θ :=
    isRotationAbout_of_param hA hI f a b ha hb hab hfix
      (Real.cos (2 * Real.pi * (m : ℝ) / (M : ℝ))) hcf θ hθ0 hθπ hθcos
  have hrot0 : Work.Mostow.IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ)) := by
    refine isRotationAbout_of_param hA hI b₀ a b ha hb hab hfixb0
      (Real.cos (2 * Real.pi / (M : ℝ))) ?_ (2 * Real.pi / (M : ℝ)) ?_ ?_ rfl
    · intro Z hZ1 hZ2
      have h := hpar 1 Z hZ1 hZ2
      simpa [show 2 * Real.pi * (1:ℝ) / (M:ℝ) = 2 * Real.pi / (M:ℝ) from by ring_nf] using h
    · positivity
    · rw [div_le_iff₀ (by positivity : (0:ℝ) < (M : ℝ))]
      nlinarith [Real.pi_pos, show (2:ℝ) ≤ (M:ℝ) from by exact_mod_cast hM2]
  -- the order bound
  have hordbound : 2 ≤ (orderOf f : ℝ) * Real.sin (θ / 2) := by
    have h := orderBound_of_pairing hA hI f a b ha hb hab
      (Real.cos (2 * Real.pi * (m : ℝ) / (M : ℝ))) hcne hcf hfin hor hax
    simpa [hθdef] using h
  -- the sin comparison
  have hsin_ge : Real.sin (Real.pi / (M : ℝ)) ≤ Real.sin (θ / 2) := by
    have h1 : Real.sin (θ / 2) ^ 2 = Real.sin (Real.pi * (m : ℝ) / (M : ℝ)) ^ 2 := by
      have h2 : Real.sin (θ / 2) ^ 2 = (1 - Real.cos θ) / 2 := by
        have h3 := Real.cos_two_mul_eq_one_sub (x := θ / 2)
        rw [show 2 * (θ / 2) = θ from by ring] at h3
        linarith
      have h4 := Real.cos_two_mul_eq_one_sub (x := Real.pi * (m : ℝ) / (M : ℝ))
      rw [show 2 * (Real.pi * (m : ℝ) / (M : ℝ)) = 2 * Real.pi * (m : ℝ) / (M : ℝ) from by ring]
        at h4
      rw [h2, hθcos, h4]
      ring
    have h3 : 0 ≤ Real.sin (θ / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have h4 : Real.sin (Real.pi * (m : ℝ) / (M : ℝ)) ≥ 0 := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · positivity
      · rw [div_le_iff₀ (by positivity : (0:ℝ) < (M:ℝ))]
        nlinarith [Real.pi_pos, show ((m:ℝ) ≤ (M:ℝ)) from by exact_mod_cast hmlt.le]
    have h5 := sin_pi_div_le M m hM2 hmpos hmlt
    have h6 : Real.sin (θ / 2) = Real.sin (Real.pi * (m : ℝ) / (M : ℝ)) := by
      rw [← Real.sqrt_sq h3, ← Real.sqrt_sq h4, h1]
    linarith [h5, h6]
  -- the inequality
  have hineq : Real.sinh (Work.Mostow.distGeod a b z) * Real.sin (θ / 2) ≤ η / 2 :=
    ineq_of_rotation hA hI f a b z ha hb hab θ η hθ0 hθπ hη hη2 hrotf hnear
  have hineq2 : Real.sinh (Work.Mostow.distGeod a b z) * Real.sin (Real.pi / (M : ℝ)) ≤ η / 2 := by
    have h1 : 0 ≤ Real.sinh (Work.Mostow.distGeod a b z) :=
      Real.sinh_nonneg_iff.mpr (distGeod_nonneg a b ha hb hab z)
    nlinarith [hineq, hsin_ge, h1]
  refine ⟨a, b, θ, M, b₀, ha, hb, hab, hθ0, hθπ, hrotf, hordbound, hMpos, hb0Γ,
    hMdef.symm, hrot0, ?_, ⟨k, hkff⟩, ?_⟩
  · intro g hgΓ hgfix
    have hsta := finite_stab hA hI Γ hΓ.1 a b (gcAxisPt a b 0)
      (gcAxisPt_mem_geodSet a b ha hb hab 0)
    have hgfin : IsOfFinOrder g := by
      by_contra h
      have hinj : Function.Injective (fun n : ℕ => g ^ n) := injective_pow_iff_not_isOfFinOrder.mpr h
      have hsub : Set.range (fun n : ℕ => g ^ n) ⊆
          {g' : LeanEval.Geometry.MostowRigidity.PO 3 1 |
            g' ∈ Γ ∧ ∀ u : Submission.Mostow.E 3, u ∈ Work.Mostow.geodSet a b → g' • u = u} := by
        rintro _ ⟨n, rfl⟩
        refine ⟨pow_mem hgΓ n, ?_⟩
        intro u hu
        have h1 : ∀ n : ℕ, (g ^ n) • u = u := by
          intro n
          induction n with
          | zero => rw [pow_zero]; exact (POBasic.ofProp hA).one_smul u
          | succ n ih => rw [pow_succ, (POBasic.ofProp hA).mul_smul, hgfix u hu, ih]
        exact h1 n
      exact Set.infinite_range_of_injective hinj (hsta.subset hsub)
    exact hgen g hgΓ hgfin hgfix
  · rw [hMdef]
    exact hineq2

end

end Work.Mostow.gapA
