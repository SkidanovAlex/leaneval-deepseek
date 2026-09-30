import Submission.Work.Pi6.EFACTS.eDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The cohomology of the cover `E = S³⟨3⟩` in degrees 5–8

The fibre `F = fib g3` of `proj g3 : E → SphModel 3` is a `K(ℤ,2)`-model through degree `11`
(`fibreRing`), so `H^{2k}(F) = ℤ·x^k`, `H^{odd}(F) = 0`, and the Wang transgression is
multiplicative (`c2_eq`, `c3eq`, `c4_high`).  Combined with the exactness spots of the Wang
sequence of the cover this computes `H⁵(E) ≅ ℤ/2`, `H⁶(E) = 0`, `H⁷(E) ≅ ℤ/3`, `H⁸(E) = 0`.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Pi6.EFACTS

noncomputable section

variable {P3 : Type} [TopologicalSpace P3] (g3 : C(S3, P3))

/-! ## The values of the transgression -/

/-- **`θ₁(x²) = 2 c₁ x`** where `c₁ = θ_{-1}(x)`. -/
lemma theta1_val (x : Coh ℤ (fib g3) 2) (m : ℤ) (hc1 : Wθlow g3 x = m • one ℤ (fib g3)) :
    Wθ g3 1 (cpow x 2) = ((2 * m : ℤ)) • x := by
  have h1 := congrArg (fun u => (Work.Pi6.cup ℤ (fib g3) 2 0 x) u) hc1
  have h2 := map_zsmul ((Work.Pi6.cup ℤ (fib g3) 2 0) x) m (one ℤ (fib g3))
  have h3 := congrArg (fun t => (m:ℤ) • t)
    (Work.Cohomology.cupH'_one_right ℤ (TopCat.toSSet.obj (TopCat.of (fib g3))) 2 x)
  have hs : (Work.Pi6.cup ℤ (fib g3) 2 0 x) (Wθlow g3 x) = m • x := h1.trans (h2.trans h3)
  exact (c2_eq g3 x).trans ((congrArg (fun u => (2:ℤ) • u) hs).trans (smul_smul 2 m x))

/-- **`θ₁(x ⌣ x) = 2 c₁ x`**. -/
lemma theta1_val' (x : Coh ℤ (fib g3) 2) (m : ℤ) (hc1 : Wθlow g3 x = m • one ℤ (fib g3)) :
    Wθ g3 1 (x2 g3 x) = ((2 * m : ℤ)) • x :=
  (congrArg (fun t => Wθ g3 1 t) (x2_eq g3 x).symm).trans (theta1_val g3 x m hc1)

/-- **`θ₃(x ⌣ x ⌣ x) = 3 c₁ x²`** (right-nested cube). -/
lemma theta3_val (x : Coh ℤ (fib g3) 2) (m : ℤ) (hc1 : Wθlow g3 x = m • one ℤ (fib g3)) :
    Wθ g3 3 (y3 g3 x) = ((3 * m : ℤ)) • (cpow x 2) := by
  have h1 := congrArg (fun u => (Work.StemsB.cupT (fib g3) 4 0 (x2 g3 x)) u) hc1
  have h2 := map_zsmul ((Work.StemsB.cupT (fib g3) 4 0 (x2 g3 x))) m (one ℤ (fib g3))
  have h3 := congrArg (fun t => (m:ℤ) • t)
    (Work.Cohomology.cupH'_one_right ℤ (TopCat.toSSet.obj (TopCat.of (fib g3))) 4 (x2 g3 x))
  have hs : (Work.StemsB.cupT (fib g3) 4 0 (x2 g3 x)) (Wθlow g3 x) = m • (x2 g3 x) :=
    h1.trans (h2.trans h3)
  exact (c3eq g3 x).trans
    ((congrArg (fun t => (3:ℕ) • t) hs).trans
      ((nsmul_zsmul_assoc 3 m (x2 g3 x)).trans
        (congrArg (fun t => ((3:ℤ)*m) • t) (x2_eq g3 x).symm)))

/-- **`θ₃(x³) = 3 c₁ x²`** on the generator `cpow x 3` of `H⁶(F)`. -/
lemma theta3_gen (x : Coh ℤ (fib g3) 2) (m : ℤ) (hc1 : Wθlow g3 x = m • one ℤ (fib g3)) :
    Wθ g3 3 (cpow x 3) = ((3 * m : ℤ)) • (cpow x 2) :=
  (congrArg (fun t => Wθ g3 3 t) (y3_eq_cpow3 g3 x).symm).trans (theta3_val g3 x m hc1)

/-- **`θ₅(x² ⌣ x²) = 4 c₁ (x ⌣ x ⌣ x)`** (high Leibniz rule `c4_high`). -/
lemma theta5_val (x : Coh ℤ (fib g3) 2) (m : ℤ) (hc1 : Wθlow g3 x = m • one ℤ (fib g3)) :
    Wθ g3 5 (z4 g3 x) = ((4 * m : ℤ)) • (y3 g3 x) := by
  have h := c4_high g3 x
  have h1 : (Work.StemsB.cupT (fib g3) 4 2 (x2 g3 x)) (Wθ g3 1 (x2 g3 x))
      = (2*m : ℤ) • (Work.StemsB.cupT (fib g3) 4 2 (x2 g3 x) x) :=
    (congrArg (fun t => (Work.StemsB.cupT (fib g3) 4 2 (x2 g3 x)) t)
      (theta1_val' g3 x m hc1)).trans
      (map_zsmul ((Work.StemsB.cupT (fib g3) 4 2 (x2 g3 x))) (2*m) x)
  have h2 : (Work.StemsB.cupT (fib g3) 2 4 (Wθ g3 1 (x2 g3 x)) (x2 g3 x))
      = (2*m : ℤ) • (Work.StemsB.cupT (fib g3) 2 4 x (x2 g3 x)) :=
    (congrArg (fun t => (Work.StemsB.cupT (fib g3) 2 4 t) (x2 g3 x))
      (theta1_val' g3 x m hc1)).trans
      ((congrArg (fun (f : Coh ℤ (fib g3) 4 →ₗ[ℤ] Coh ℤ (fib g3) 6) => f (x2 g3 x))
        (map_zsmul (Work.StemsB.cupT (fib g3) 2 4) (2*m) x)).trans rfl)
  refine h.trans ?_
  rw [h1, h2, x2x_eq]
  exact (show (2*m : ℤ) • (y3 g3 x) + (2*m : ℤ) • (y3 g3 x) = ((4*m : ℤ)) • (y3 g3 x) from by
    rw [← add_zsmul, show (2*m + 2*m : ℤ) = 4*m from by ring])

/-- **`θ₅(x⁴) = 4 c₁ x³`** on the generator `cpow x 4` of `H⁸(F)`. -/
lemma theta5_gen (x : Coh ℤ (fib g3) 2) (m : ℤ) (hc1 : Wθlow g3 x = m • one ℤ (fib g3)) :
    Wθ g3 5 (cpow x 4) = ((4 * m : ℤ)) • (cpow x 3) :=
  (congrArg (fun t => Wθ g3 5 t) (cpow4_eq g3 x)).trans
    ((theta5_val g3 x m hc1).trans (congrArg (fun t => (4*m : ℤ) • t) (y3_eq_cpow3 g3 x)))

/-! ## The coefficient of a cyclic module -/

/-- The coefficient of `a` as a multiple of the generator `g`. -/
noncomputable def genCoef {n : ℕ} (g : Coh ℤ (fib g3) n)
    (hgen : ∀ a : Coh ℤ (fib g3) n, ∃! k : ℤ, a = k • g) (a : Coh ℤ (fib g3) n) : ℤ :=
  Classical.choose (hgen a)

lemma genCoef_spec {n : ℕ} (g : Coh ℤ (fib g3) n)
    (hgen : ∀ a : Coh ℤ (fib g3) n, ∃! k : ℤ, a = k • g) (a : Coh ℤ (fib g3) n) :
    a = genCoef g3 g hgen a • g :=
  (Classical.choose_spec (hgen a)).1

lemma genCoef_unique {n : ℕ} (g : Coh ℤ (fib g3) n)
    (hgen : ∀ a : Coh ℤ (fib g3) n, ∃! k : ℤ, a = k • g) (a : Coh ℤ (fib g3) n) (k : ℤ)
    (hk : a = k • g) : k = genCoef g3 g hgen a :=
  (Classical.choose_spec (hgen a)).2 k hk

lemma genCoef_zsmul {n : ℕ} (g : Coh ℤ (fib g3) n)
    (hgen : ∀ a : Coh ℤ (fib g3) n, ∃! k : ℤ, a = k • g) (k : ℤ) :
    genCoef g3 g hgen (k • g) = k :=
  (genCoef_unique g3 g hgen (k • g) k rfl).symm

/-- **`M ⧸ ℤ•(c • g) ≅ ZMod c`** for a cyclic `M = ℤ·g` (`c > 0`). -/
lemma quotient_gen_iso {n : ℕ} (g : Coh ℤ (fib g3) n)
    (hgen : ∀ a : Coh ℤ (fib g3) n, ∃! k : ℤ, a = k • g) (c : ℕ) (hc : 0 < c) :
    Nonempty (((Coh ℤ (fib g3) n : Type) ⧸ AddSubgroup.zmultiples ((c:ℤ) • g)) ≃+ ZMod c) := by
  haveI : NeZero c := ⟨Nat.pos_iff_ne_zero.mp hc⟩
  let coef : (Coh ℤ (fib g3) n : Type) →+ ℤ := AddMonoidHom.mk'
    (genCoef g3 g hgen) (by
      intro a b
      have h : a + b = (genCoef g3 g hgen a + genCoef g3 g hgen b) • g := by
        conv_lhs => rw [genCoef_spec g3 g hgen a, genCoef_spec g3 g hgen b]
        rw [← add_zsmul]
      exact (genCoef_unique g3 g hgen (a + b) _ h).symm)
  let f : (Coh ℤ (fib g3) n : Type) →+ ZMod c := (Int.castAddHom (ZMod c)).comp coef
  have hf : Function.Surjective f := by
    intro z
    refine ⟨((z.val : ℕ) : ℤ) • g, ?_⟩
    show (((genCoef g3 g hgen (((z.val : ℕ) : ℤ) • g)) : ℤ) : ZMod c) = z
    rw [genCoef_zsmul g3 g hgen, Int.cast_natCast]
    exact ZMod.natCast_zmod_val z
  have hker : f.ker = AddSubgroup.zmultiples ((c:ℤ) • g) := by
    ext a
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_zmultiples_iff]
    show (((genCoef g3 g hgen a : ℤ)) : ZMod c) = 0 ↔ _
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := h
      refine ⟨k, ?_⟩
      rw [genCoef_spec g3 g hgen a, hk, smul_smul, mul_comm]
    · rintro ⟨k, hk⟩
      exact ⟨k, (genCoef_unique g3 g hgen a (k * ↑c) (by rw [← hk, smul_smul])).symm.trans
        (by rw [mul_comm])⟩
  exact ⟨(QuotientAddGroup.quotientAddEquivOfEq hker).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f hf)⟩

/-! ## Elementary conversions and exactness spots -/

/-- `ℤ•((-c) • x) = ℤ•(c • x)`. -/
lemma zmultiples_zsmul_neg {M : Type} [AddCommGroup M] [Module ℤ M] (c : ℤ) (x : M) :
    AddSubgroup.zmultiples ((-c) • x) = AddSubgroup.zmultiples (c • x) := by
  ext a
  rw [AddSubgroup.mem_zmultiples_iff, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    rw [← hk, smul_smul, smul_smul]
    congr 1
    ring
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    rw [← hk, smul_smul, smul_smul]
    congr 1
    ring

/-- The image of a linear map is the kernel of the next map in an exact sequence. -/
lemma ker_eq_range {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module ℤ M] [Module ℤ N] [Module ℤ P] (f : M →ₗ[ℤ] N) (g : N →ₗ[ℤ] P)
    (h : ∀ y, g y = 0 ↔ y ∈ Set.range f) : g.ker = f.range := by
  ext y
  rw [LinearMap.mem_ker, LinearMap.mem_range, ← Set.mem_range]
  exact h y

/-- **`β_n` is surjective** as soon as `H^{n+4}(F) = 0`. -/
lemma Wβ_surj (n : ℕ) (hsub : Subsingleton (Coh ℤ (fib g3) (n + 4))) :
    Function.Surjective (Wβ g3 n).hom := by
  haveI := hsub
  intro y
  have h := wangExactTot 3 (by norm_num) (proj g3) (hTO g3) shellPt (hTG g3) n y
  have h0 : (Wα g3 (n + 4)).hom y = (0 : Coh ℤ (fib g3) (n + 4)) := Subsingleton.elim _ _
  have h1 := h.mp h0
  rw [Set.mem_range] at h1
  exact h1

/-- **`β_n = 0`** as soon as `H^{n+1}(F) = 0`. -/
lemma Wβ_eq_zero (n : ℕ) (hsub : Subsingleton (Coh ℤ (fib g3) (n + 1))) : Wβ g3 n = 0 := by
  haveI := hsub
  apply ModuleCat.hom_ext
  ext y
  rw [show y = 0 from Subsingleton.elim y 0]
  exact map_zero _

/-- **`θ_{-1}(x) = ±1`**: the low transgression is an isomorphism `H²(F) ≅ H⁰(F)`. -/
lemma c1_pm (x : Coh ℤ (fib g3) 2) (m : ℤ) (hc1 : Wθlow g3 x = m • one ℤ (fib g3))
    (hsurj : Function.Surjective (Wθlow g3))
    (hgen2 : ∀ a : Coh ℤ (fib g3) 2, ∃! k : ℤ, a = k • x)
    (hgen0 : ∀ a : Coh ℤ (fib g3) 0, ∃! k : ℤ, a = k • one ℤ (fib g3)) :
    m = 1 ∨ m = -1 := by
  obtain ⟨y, hy⟩ := hsurj (one ℤ (fib g3))
  obtain ⟨k, hk, -⟩ := hgen2 y
  have hstep : (Wθlow g3) (k • x) = (k * m) • one ℤ (fib g3) := by
    rw [map_zsmul, hc1, smul_smul]
  have h1 : one ℤ (fib g3) = (k * m) • one ℤ (fib g3) :=
    (hy.symm.trans (by rw [hk])).trans hstep
  obtain ⟨n, -, huniq⟩ := hgen0 (one ℤ (fib g3))
  have hn1 : n = 1 := (huniq 1 (one_zsmul _).symm).symm
  have hkm : k * m = 1 := by
    have h := huniq (k * m) h1
    rw [hn1] at h
    exact h
  rcases (Int.mul_eq_one_iff_eq_one_or_neg_one.mp hkm) with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h



/-! ## The computation of `H^*(E)` in degrees 5–8 -/

/-- **The cohomology of the cover `E = S³⟨3⟩` in degrees 5 to 8.** -/
theorem eCohCore (g3 : C(S3, P3)) (hP3 : PostnikovData 3 12 g3 s3)
    (hfib : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) 11 (fib g3) (fibPt g3))
    (hZ : K2ZFacts) :
    Nonempty (Coh ℤ (Ecov g3) 5 ≃ₗ[ℤ] ZMod 2) ∧ Subsingleton (Coh ℤ (Ecov g3) 6) ∧
      Nonempty (Coh ℤ (Ecov g3) 7 ≃ₗ[ℤ] ZMod 3) ∧ Subsingleton (Coh ℤ (Ecov g3) 8) := by
  obtain ⟨x, hx, hmult, hodd⟩ := fibreRing g3 (fibPt g3) hfib hZ
  have hgen0 : ∀ a : Coh ℤ (fib g3) 0, ∃! k : ℤ, a = k • one ℤ (fib g3) :=
    fun a => hmult 0 (by norm_num) a
  have hgen1 : ∀ a : Coh ℤ (fib g3) 2, ∃! k : ℤ, a = k • x := by
    intro a
    obtain ⟨k, hk, hu⟩ := hmult 1 (by norm_num) a
    refine ⟨k, ?_, fun l hl => hu l ?_⟩
    · rw [cpow_one_eq x] at hk; exact hk
    · rw [cpow_one_eq x]; exact hl
  have hgen2 : ∀ a : Coh ℤ (fib g3) 4, ∃! k : ℤ, a = k • (cpow x 2) :=
    fun a => hmult 2 (by norm_num) a
  have hgen3 : ∀ a : Coh ℤ (fib g3) 6, ∃! k : ℤ, a = k • (cpow x 3) :=
    fun a => hmult 3 (by norm_num) a
  have hgen4 : ∀ a : Coh ℤ (fib g3) 8, ∃! k : ℤ, a = k • (cpow x 4) :=
    fun a => hmult 4 (by norm_num) a
  obtain ⟨m, hm, -⟩ := hgen0 (Wθlow g3 x)
  have hm1 : m = 1 ∨ m = -1 := c1_pm g3 x m hm (Wθlow_surj g3 hP3) hgen1 hgen0
  have h2m : (2:ℤ) * m ≠ 0 := by rcases hm1 with h | h <;> rw [h] <;> norm_num
  have h3m : (3:ℤ) * m ≠ 0 := by rcases hm1 with h | h <;> rw [h] <;> norm_num
  have h4m : (4:ℤ) * m ≠ 0 := by rcases hm1 with h | h <;> rw [h] <;> norm_num
  have hθ1 := theta1_val g3 x m hm
  have hθ3 := theta3_gen g3 x m hm
  have hθ5 := theta5_gen g3 x m hm
  -- the three kernels vanish
  have hker1 : LinearMap.ker (Wθ g3 1) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro a ha
    rw [LinearMap.mem_ker] at ha
    obtain ⟨k, hk, -⟩ := hgen2 a
    rw [hk, map_zsmul, hθ1, smul_smul] at ha
    have hk0 : k * ((2:ℤ) * m) = 0 := by
      obtain ⟨j, -, huniq⟩ := hgen1 (0 : Coh ℤ (fib g3) 2)
      exact (huniq (k * ((2:ℤ) * m)) ha.symm).trans (huniq 0 (zero_smul ℤ x).symm).symm
    have hkz : k = 0 := by
      rcases mul_eq_zero.mp hk0 with h | h
      · exact h
      · exact absurd h h2m
    rw [hk, hkz, zero_smul]
  have hker3 : LinearMap.ker (Wθ g3 3) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro a ha
    rw [LinearMap.mem_ker] at ha
    obtain ⟨k, hk, -⟩ := hgen3 a
    rw [hk, map_zsmul, hθ3, smul_smul] at ha
    have hk0 : k * ((3:ℤ) * m) = 0 := by
      obtain ⟨j, -, huniq⟩ := hgen2 (0 : Coh ℤ (fib g3) 4)
      exact (huniq (k * ((3:ℤ) * m)) ha.symm).trans (huniq 0 (zero_smul ℤ (cpow x 2)).symm).symm
    have hkz : k = 0 := by
      rcases mul_eq_zero.mp hk0 with h | h
      · exact h
      · exact absurd h h3m
    rw [hk, hkz, zero_smul]
  have hker5 : LinearMap.ker (Wθ g3 5) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro a ha
    rw [LinearMap.mem_ker] at ha
    obtain ⟨k, hk, -⟩ := hgen4 a
    rw [hk, map_zsmul, hθ5, smul_smul] at ha
    have hk0 : k * ((4:ℤ) * m) = 0 := by
      obtain ⟨j, -, huniq⟩ := hgen3 (0 : Coh ℤ (fib g3) 6)
      exact (huniq (k * ((4:ℤ) * m)) ha.symm).trans (huniq 0 (zero_smul ℤ (cpow x 3)).symm).symm
    have hkz : k = 0 := by
      rcases mul_eq_zero.mp hk0 with h | h
      · exact h
      · exact absurd h h4m
    rw [hk, hkz, zero_smul]
  -- the two ranges
  have hrange1' : (Wθ g3 1).range.toAddSubgroup =
      AddSubgroup.zmultiples (((2:ℤ) * m) • x) := by
    ext a
    show a ∈ (Wθ g3 1).range ↔ a ∈ AddSubgroup.zmultiples (((2:ℤ) * m) • x)
    rw [LinearMap.mem_range, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨b, rfl⟩
      obtain ⟨k, hk, -⟩ := hgen2 b
      exact ⟨k, by rw [hk, map_zsmul, hθ1]⟩
    · rintro ⟨k, hk⟩
      exact ⟨k • cpow x 2, by rw [map_zsmul, hθ1]; exact hk⟩
  have hspan1 : AddSubgroup.zmultiples (((2:ℤ) * m) • x) =
      AddSubgroup.zmultiples ((2:ℤ) • x) := by
    rcases hm1 with h | h
    · rw [h]; norm_num
    · rw [h]
      have h2 : (2 * (-1:ℤ)) = (-2:ℤ) := by norm_num
      rw [h2]
      exact zmultiples_zsmul_neg 2 x
  have hrange3' : (Wθ g3 3).range.toAddSubgroup =
      AddSubgroup.zmultiples (((3:ℤ) * m) • (cpow x 2)) := by
    ext a
    show a ∈ (Wθ g3 3).range ↔ a ∈ AddSubgroup.zmultiples (((3:ℤ) * m) • (cpow x 2))
    rw [LinearMap.mem_range, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨b, rfl⟩
      obtain ⟨k, hk, -⟩ := hgen3 b
      exact ⟨k, by rw [hk, map_zsmul, hθ3]⟩
    · rintro ⟨k, hk⟩
      exact ⟨k • cpow x 3, by rw [map_zsmul, hθ3]; exact hk⟩
  have hspan3 : AddSubgroup.zmultiples (((3:ℤ) * m) • (cpow x 2)) =
      AddSubgroup.zmultiples ((3:ℤ) • (cpow x 2)) := by
    rcases hm1 with h | h
    · rw [h]; norm_num
    · rw [h]
      have h3 : (3 * (-1:ℤ)) = (-3:ℤ) := by norm_num
      rw [h3]
      exact zmultiples_zsmul_neg 3 (cpow x 2)
  -- H⁵(E) ≅ ℤ/2
  have hF5 : Subsingleton (Coh ℤ (fib g3) 5) := hodd 2 (by norm_num)
  have hβ1surj : Function.Surjective (Wβ g3 1).hom := Wβ_surj g3 1 hF5
  have hkerβ1 : LinearMap.ker (Wβ g3 1).hom = (Wθ g3 1).range :=
    ker_eq_range (Wθ g3 1) (Wβ g3 1).hom
      (fun y => (wangExact₃ 3 (by norm_num) (proj g3) (hTO g3) shellPt (hTG g3) 1) y)
  have hH1 : (LinearMap.ker (Wβ g3 1).hom).toAddSubgroup =
      AddSubgroup.zmultiples ((2:ℤ) • x) := by
    rw [hkerβ1]; exact hrange1'.trans hspan1
  obtain ⟨eQ1⟩ := quotient_gen_iso g3 x hgen1 2 (by norm_num)
  have e5 : (Coh ℤ (Ecov g3) 5 : Type) ≃+ ZMod 2 :=
    (QuotientAddGroup.quotientKerEquivOfSurjective ((Wβ g3 1).hom.toAddMonoidHom)
      hβ1surj).symm.trans ((QuotientAddGroup.quotientAddEquivOfEq hH1).trans eQ1)
  -- H⁶(E) = 0
  have hF3 : Subsingleton (Coh ℤ (fib g3) 3) := hodd 1 (by norm_num)
  have hβ2 : Wβ g3 2 = 0 := Wβ_eq_zero g3 2 hF3
  have hα6ker : LinearMap.ker (Wα g3 6).hom = ⊥ := by
    rw [ker_eq_range (Wβ g3 2).hom (Wα g3 6).hom
      (fun y => (wangExactTot 3 (by norm_num) (proj g3) (hTO g3) shellPt (hTG g3) 2) y), hβ2]
    simp
  have hinj6 : Function.Injective (Wα g3 6).hom := LinearMap.ker_eq_bot.mp hα6ker
  have hα6zero : (Wα g3 6).hom = 0 := by
    have h := ker_eq_range (Wα g3 6).hom (Wθ g3 3)
      (fun z => (wangExact₂ 3 (by norm_num) (proj g3) (hTO g3) shellPt (hTG g3) 3) z)
    have h2 : (Wα g3 6).hom.range = ⊥ := by rw [← h, hker3]
    exact LinearMap.range_eq_bot.mp h2
  have h6 : Subsingleton (Coh ℤ (Ecov g3) 6) :=
    ⟨fun p q => hinj6 (by rw [hα6zero]; simp)⟩
  -- H⁷(E) ≅ ℤ/3
  have hF7 : Subsingleton (Coh ℤ (fib g3) 7) := hodd 3 (by norm_num)
  have hβ3surj : Function.Surjective (Wβ g3 3).hom := Wβ_surj g3 3 hF7
  have hkerβ3 : LinearMap.ker (Wβ g3 3).hom = (Wθ g3 3).range :=
    ker_eq_range (Wθ g3 3) (Wβ g3 3).hom
      (fun y => (wangExact₃ 3 (by norm_num) (proj g3) (hTO g3) shellPt (hTG g3) 3) y)
  have hH3 : (LinearMap.ker (Wβ g3 3).hom).toAddSubgroup =
      AddSubgroup.zmultiples ((3:ℤ) • (cpow x 2)) := by
    rw [hkerβ3]; exact hrange3'.trans hspan3
  obtain ⟨eQ3⟩ := quotient_gen_iso g3 (cpow x 2) hgen2 3 (by norm_num)
  have e7 : (Coh ℤ (Ecov g3) 7 : Type) ≃+ ZMod 3 :=
    (QuotientAddGroup.quotientKerEquivOfSurjective ((Wβ g3 3).hom.toAddMonoidHom)
      hβ3surj).symm.trans ((QuotientAddGroup.quotientAddEquivOfEq hH3).trans eQ3)
  -- H⁸(E) = 0
  have hβ4 : Wβ g3 4 = 0 := Wβ_eq_zero g3 4 hF5
  have hα8ker : LinearMap.ker (Wα g3 8).hom = ⊥ := by
    rw [ker_eq_range (Wβ g3 4).hom (Wα g3 8).hom
      (fun y => (wangExactTot 3 (by norm_num) (proj g3) (hTO g3) shellPt (hTG g3) 4) y), hβ4]
    simp
  have hinj8 : Function.Injective (Wα g3 8).hom := LinearMap.ker_eq_bot.mp hα8ker
  have hα8zero : (Wα g3 8).hom = 0 := by
    have h := ker_eq_range (Wα g3 8).hom (Wθ g3 5)
      (fun z => (wangExact₂ 3 (by norm_num) (proj g3) (hTO g3) shellPt (hTG g3) 5) z)
    have h2 : (Wα g3 8).hom.range = ⊥ := by rw [← h, hker5]
    exact LinearMap.range_eq_bot.mp h2
  have h8 : Subsingleton (Coh ℤ (Ecov g3) 8) :=
    ⟨fun p q => hinj8 (by rw [hα8zero]; simp)⟩
  exact ⟨⟨AddEquiv.toIntLinearEquiv e5⟩, h6, ⟨AddEquiv.toIntLinearEquiv e7⟩, h8⟩

end

end Work.Pi6.EFACTS
