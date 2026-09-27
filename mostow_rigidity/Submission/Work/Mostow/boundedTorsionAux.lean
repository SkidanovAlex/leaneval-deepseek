import Mathlib
import Submission.Mostow.HLDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.StabLift
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.geomFiniteParabolicClass
import Submission.Work.Mostow.finite_nearStab_compact
import Submission.Work.Mostow.geomFiniteThickThinDefs
import Submission.Work.Mostow.thinTubeDefs
import Submission.Work.Mostow.exists_closest_orbit
import Submission.Work.Mostow.bieberbach

/-!
# `boundedTorsion` — the sorry-free auxiliary lemmas

Contents (all sorry-free):

* `bt_mink_add_left/right`, `bt_mink_sum_left/right` — bilinearity of the Minkowski form;
* `fixPoint_of_finite` — **L1**: a finite subgroup of `PO n 1` fixes a point of `ℍⁿ`;
* `card_le_of_fix_near_compact` — **L3**: if the fixed point can be moved into a fixed compact set,
  the order of the finite subgroup is bounded;
* `bt_not_thinParabolic_cocompact` — **L2**: the complement of the parabolically thin part of a
  lattice is `Γ`-cocompact (from the two cuspidal inputs `deep_mem_thinParabolic` and
  `dirichlet_notDeep_bounded`);
* `CuspTorsionBound` and `boundedTorsion_of_cuspStructure` — the assembly: L1 + L2 + L3 + L4 give
  `BoundedTorsion Γ`.

The remaining mathematical input L4 (`CuspTorsionBound`) is the cusp-stabiliser torsion bound; see
`boundedTorsion_NOTES.md`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## Bilinearity of the Minkowski form (local, self-contained) -/

lemma bt_mink_add_left (x y z : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.mink (x + y) z = Hyper.mink x z + Hyper.mink y z := by
  simp only [Hyper.mink, add_dotProduct]

lemma bt_mink_add_right (x y z : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.mink x (y + z) = Hyper.mink x y + Hyper.mink x z := by
  simp only [Hyper.mink, Matrix.mulVec_add, dotProduct_add]

lemma bt_mink_sum_left {ι : Type*} (s : Finset ι) (f : ι → (Fin n ⊕ Fin 1 → ℝ))
    (y : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.mink (∑ i ∈ s, f i) y = ∑ i ∈ s, Hyper.mink (f i) y := by
  classical
  induction s using Finset.induction with
  | empty => simp [Hyper.mink]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, bt_mink_add_left, ih]

lemma bt_mink_sum_right {ι : Type*} (s : Finset ι) (x : Fin n ⊕ Fin 1 → ℝ)
    (f : ι → (Fin n ⊕ Fin 1 → ℝ)) :
    Hyper.mink x (∑ i ∈ s, f i) = ∑ i ∈ s, Hyper.mink x (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [Hyper.mink]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, bt_mink_add_right, ih]

/-! ## L1: a finite subgroup of `PO n 1` has a fixed point -/

/-- **L1.** A finite subgroup of `PO n 1` fixes a point of `ℍⁿ`. -/
theorem fixPoint_of_finite (hA : POActionProp n) (F : Subgroup (PO n 1)) (hF : Finite F) :
    ∃ p : E n, ∀ f ∈ F, f • p = p := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Nonempty F := ⟨1⟩
  -- the average of the orbit of the origin in the hyperboloid model
  set v : Fin n ⊕ Fin 1 → ℝ := ∑ f : F, hlift ((f : PO n 1) • (0 : E n)) with hv
  have htime : 0 < v (Sum.inr 0) := by
    rw [hv, Finset.sum_apply]
    have hpos : 0 < ∑ f : F, tpart ((f : PO n 1) • (0 : E n)) :=
      Finset.sum_pos (fun f _ => tpart_pos _) Finset.univ_nonempty
    simpa [hlift] using hpos
  have hcard : (1 : ℝ) ≤ (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := F)
  have hminkneg : Hyper.mink v v < 0 := by
    rw [hv, bt_mink_sum_left]
    have hstep : ∀ f : F,
        ∑ g : F, Hyper.mink (hlift ((f : PO n 1) • (0 : E n)))
            (hlift ((g : PO n 1) • (0 : E n))) ≤ -1 := by
      intro f
      have h1 : ∀ g : F,
          Hyper.mink (hlift ((f : PO n 1) • (0 : E n)))
            (hlift ((g : PO n 1) • (0 : E n))) ≤ -1 := by
        intro g
        rw [Hyper.mink_hlift]
        have h2 := one_le_cosh_hdist ((f : PO n 1) • (0 : E n)) ((g : PO n 1) • (0 : E n))
        linarith
      calc ∑ g : F, Hyper.mink (hlift ((f : PO n 1) • (0 : E n)))
              (hlift ((g : PO n 1) • (0 : E n)))
          ≤ ∑ _g : F, (-1 : ℝ) := Finset.sum_le_sum (fun g _ => h1 g)
        _ = -((Fintype.card F : ℕ) : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              ring
        _ ≤ -1 := by linarith
    have hle : ∑ f : F, Hyper.mink (hlift ((f : PO n 1) • (0 : E n))) v ≤ -1 := by
      calc ∑ f : F, Hyper.mink (hlift ((f : PO n 1) • (0 : E n))) v
          ≤ ∑ _f : F, (-1 : ℝ) := by
            refine Finset.sum_le_sum (fun f _ => ?_)
            rw [hv, bt_mink_sum_right]
            exact hstep f
        _ = -((Fintype.card F : ℕ) : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              ring
        _ ≤ -1 := by linarith
    linarith
  set μ : ℝ := Real.sqrt (-(Hyper.mink v v)) with hμ
  have hμpos : 0 < μ := by
    rw [hμ]; exact Real.sqrt_pos.mpr (neg_pos.mpr hminkneg)
  have hμsq : μ * μ = -(Hyper.mink v v) := by
    rw [hμ, Real.mul_self_sqrt (le_of_lt (neg_pos.mpr hminkneg))]
  set y : Fin n ⊕ Fin 1 → ℝ := μ⁻¹ • v with hy
  have hminky : Hyper.mink y y = -1 := by
    rw [hy, Hyper.mink_smul]
    have hvμ : Hyper.mink v v = -(μ * μ) := by linarith [hμsq]
    rw [hvμ, mul_neg]
    have h : μ⁻¹ * μ⁻¹ * (μ * μ) = 1 := by
      rw [show μ⁻¹ * μ⁻¹ * (μ * μ) = (μ⁻¹ * μ) * (μ⁻¹ * μ) by ring,
        inv_mul_cancel₀ (ne_of_gt hμpos), mul_one]
    rw [h]
  have hypos : 0 < y (Sum.inr 0) := by
    rw [hy, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.mpr hμpos) htime
  -- the average is fixed by the lift of every element of `F`
  have hfixv : ∀ g : F, Matrix.mulVec (LambdaMat ((g : F) : PO n 1)) v = v := by
    intro g
    rw [hv, Matrix.mulVec_sum]
    have hstep : ∀ f : F,
        Matrix.mulVec (LambdaMat ((g : F) : PO n 1)) (hlift (((f : F) : PO n 1) • (0 : E n)))
          = hlift ((((g : F) : PO n 1) * ((f : F) : PO n 1)) • (0 : E n)) := by
      intro f
      rw [← hlift_LambdaMat hA, hA.2.2.2.2.1]
    rw [Finset.sum_congr rfl (fun f _ => hstep f)]
    exact Equiv.sum_comp (Equiv.mulLeft g)
      (fun f : F => hlift (((f : F) : PO n 1) • (0 : E n)))
  refine ⟨Hyper.spat y, fun f hf => ?_⟩
  have hylift : hlift (Hyper.spat y) = y := Hyper.hlift_spat_of_mink y hminky hypos
  have hkey : hlift (((⟨f, hf⟩ : F) : PO n 1) • Hyper.spat y) = hlift (Hyper.spat y) := by
    rw [hylift, hlift_LambdaMat hA, hylift, hy]
    have hsmul : Matrix.mulVec (LambdaMat (((⟨f, hf⟩ : F)) : PO n 1)) (μ⁻¹ • v)
        = μ⁻¹ • (Matrix.mulVec (LambdaMat (((⟨f, hf⟩ : F)) : PO n 1)) v) := by
      simpa only [mulVecLin_apply] using
        map_smul (mulVecLin (LambdaMat (((⟨f, hf⟩ : F)) : PO n 1))) μ⁻¹ v
    rw [hsmul, hfixv ⟨f, hf⟩]
  exact Hyper.hlift_injective hkey

/-! ## L3: the order is bounded when the fixed point can be moved into a compact set -/

/-- **L3.** If the fixed point `p` of a finite subgroup `F ≤ Γ` can be moved into a fixed compact
set `K`, then `|F|` is bounded in terms of `K` and `Γ`. -/
theorem card_le_of_fix_near_compact (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ))
    (K : Set (E n)) (hKc : IsCompact K) :
    ∃ b : ℕ, ∀ F : Subgroup (PO n 1), F ≤ Γ → Finite F → ∀ p : E n,
      (∀ f ∈ F, f • p = p) → (∃ γ ∈ Γ, γ • p ∈ K) → Nat.card F ≤ b := by
  classical
  have hAb : POBasic n := POBasic.ofProp hA
  have hId : HypIsoData n := HypIsoData.ofProp hI
  set S : Set Γ := {γ : Γ | ∃ u ∈ K, ((γ : Γ) : PO n 1) • u ∈ K} with hS
  have hSfin : S.Finite := by
    have h := finite_nearStab_compact hAb hId hdisc hKc hKc
    simpa [hS, Set.mem_ofPred_eq] using h
  haveI : Fintype S := hSfin.fintype
  refine ⟨Fintype.card S, ?_⟩
  intro F hFG hFfin p hpfix hnear
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨γ₀, hγ₀Γ, hγ₀K⟩ := hnear
  -- conjugation by `γ₀` maps `F` into `S`
  have hmaps : ∀ f : F,
      (⟨(γ₀ * ((f : F) : PO n 1) * γ₀⁻¹),
        mul_mem (mul_mem hγ₀Γ (hFG f.2)) (inv_mem hγ₀Γ)⟩ : Γ) ∈ S := by
    intro f
    refine ⟨γ₀ • p, hγ₀K, ?_⟩
    show (γ₀ * ((f : F) : PO n 1) * γ₀⁻¹) • (γ₀ • p) ∈ K
    rw [hA.2.2.2.2.1, hA.2.2.2.2.1, ← hA.2.2.2.2.1 γ₀⁻¹ γ₀ p, inv_mul_cancel, hA.2.2.2.1]
    rw [hpfix f f.2]
    exact hγ₀K
  have hinj : Function.Injective
      (fun f : F => (⟨⟨(γ₀ * ((f : F) : PO n 1) * γ₀⁻¹),
        mul_mem (mul_mem hγ₀Γ (hFG f.2)) (inv_mem hγ₀Γ)⟩, hmaps f⟩ : S)) := by
    intro f₁ f₂ h
    have h' : (γ₀ * ((f₁ : F) : PO n 1) * γ₀⁻¹) = (γ₀ * ((f₂ : F) : PO n 1) * γ₀⁻¹) := by
      simpa using congrArg (fun s : S => ((s : Γ) : PO n 1)) h
    have h'' : ((f₁ : F) : PO n 1) = ((f₂ : F) : PO n 1) := by
      have := congrArg (fun x : PO n 1 => γ₀⁻¹ * x * γ₀) h'
      simpa [mul_assoc] using this
    exact Subtype.ext h''
  have hle : Nat.card F ≤ Fintype.card S := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective _ hinj
  exact hle


/-! ## The complement of the parabolically thin part is cocompact -/

lemma bt_cocompactUnder_mono {Γ : Subgroup (PO n 1)} {S T : Set (E n)} (hST : S ⊆ T)
    (hT : IsCocompactUnder Γ T) : IsCocompactUnder Γ S := by
  obtain ⟨K, hKc, hK⟩ := hT
  exact ⟨K, hKc, fun u hu => hK u (hST hu)⟩

lemma bt_thinParabolic_smul_mem (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (ε : ℝ) (δ : Γ) {u : E n} (hu : u ∈ ThinParabolic Γ ε) :
    ((δ : Γ) : PO n 1) • u ∈ ThinParabolic Γ ε := by
  obtain ⟨γ, hpar, hd⟩ := hu
  refine ⟨⟨((δ : Γ) : PO n 1) * (γ : PO n 1) * ((δ : Γ) : PO n 1)⁻¹,
      mul_mem (mul_mem δ.2 γ.2) (inv_mem δ.2)⟩, ?_, ?_⟩
  · exact isParabolic_conj hA hI ((δ : Γ) : PO n 1) (γ : PO n 1) hpar
  · rw [hdist_conj hA hI ((δ : Γ) : PO n 1) (γ : PO n 1) u]
    exact hd

lemma bt_exists_smul_mem_dirichlet (hA : POActionProp n) (hI : HypIsometryProp n)
    {Γ : Subgroup (PO n 1)} (hdisc : IsDiscrete (SetLike.coe Γ)) (u : E n) :
    ∃ δ : Γ, ((δ : Γ) : PO n 1) • u ∈ Dirichlet Γ := by
  obtain ⟨γ, hγ⟩ := exists_closest_orbit n hA hI hdisc u (0 : E n)
  refine ⟨γ, ?_⟩
  intro δ
  rw [← hA.2.2.2.2.1]
  exact hγ (δ * γ)

/-- **L2.** If deep cusp points are parabolically thin and the part of the Dirichlet domain outside
the deep cusps is bounded, then the complement of the parabolically thin part is `Γ`-cocompact. -/
theorem bt_not_thinParabolic_cocompact (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n)
    (hI : HypIsometryProp n) (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ) (ε : ℝ) (hε : 0 < ε)
    (hdeep : ∃ Y : ℝ, ∀ u : E n, (∃ ξ ∈ parFixed Γ, busemann ξ u < Y) → u ∈ ThinParabolic Γ ε)
    (hdir : ∀ Y : ℝ, ∃ R : ℝ, ∀ u : E n, u ∈ Dirichlet Γ →
      (∀ ξ ∈ parFixed Γ, Y ≤ busemann ξ u) → hdist (0 : E n) u ≤ R) :
    IsCocompactUnder Γ ((ThinParabolic Γ ε)ᶜ) := by
  have hdisc : IsDiscrete (SetLike.coe Γ) := hΓ.1
  obtain ⟨Y, hY⟩ := hdeep
  obtain ⟨R, hR⟩ := hdir Y
  refine ⟨{u : E n | hdist (0 : E n) u ≤ R}, hI.2.2.2.2.2.1 (0 : E n) R, ?_⟩
  intro u hu
  obtain ⟨δ, hδ⟩ := bt_exists_smul_mem_dirichlet hA hI hdisc u
  have hu' : ((δ : Γ) : PO n 1) • u ∉ ThinParabolic Γ ε := by
    intro hc
    have h2 : (((δ⁻¹ : Γ)) : PO n 1) • (((δ : Γ) : PO n 1) • u) ∈ ThinParabolic Γ ε :=
      bt_thinParabolic_smul_mem hA hI Γ ε δ⁻¹ hc
    have h3 : (((δ⁻¹ : Γ)) : PO n 1) • (((δ : Γ) : PO n 1) • u) = u := by
      rw [← hA.2.2.2.2.1]
      have h4 : (((δ⁻¹ : Γ)) : PO n 1) * (((δ : Γ)) : PO n 1) = 1 := by
        rw [show (((δ⁻¹ : Γ)) : PO n 1) = (((δ : Γ)) : PO n 1)⁻¹ from rfl, inv_mul_cancel]
      rw [h4, hA.2.2.2.1]
    rw [h3] at h2
    exact hu h2
  have hdepth : ∀ ξ ∈ parFixed Γ, Y ≤ busemann ξ (((δ : Γ) : PO n 1) • u) := by
    intro ξ hξ
    by_contra hlt
    exact hu' (hY _ ⟨ξ, hξ, not_le.mp hlt⟩)
  exact ⟨δ, hR _ hδ hdepth⟩

/-! ## L4 (as a hypothesis) and the assembly -/

/-- **L4 (input).** Finite subgroups of the cusp stabilisers of `Γ` are bounded uniformly over the
parabolic fixed points. -/
def CuspTorsionBound (Γ : Subgroup (PO n 1)) : Prop :=
  ∃ b : ℕ, ∀ ξ : E n, ξ ∈ parFixed Γ → ∀ F : Subgroup (PO n 1), F ≤ Γ → Finite F →
    (∀ f ∈ F, bd f ξ = ξ) → Nat.card F ≤ b

/-- **Assembly.** L1 (a finite subgroup has a fixed point), L2 (the complement of the parabolically
thin part is cocompact), L3 (a finite subgroup whose fixed point can be moved into a compact set is
bounded) and L4 (the cusp-stabiliser torsion bound) give `BoundedTorsion Γ`. -/
theorem boundedTorsion_of_cuspStructure (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n)
    (hI : HypIsometryProp n) (hM : MargulisCuspProp n) (Γ : Subgroup (PO n 1))
    (hΓ : HypLattice Γ)
    (hdeep : ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ u : E n,
      (∃ ξ ∈ parFixed Γ, busemann ξ u < Y) → u ∈ ThinParabolic Γ ε)
    (hdir : ∀ Y : ℝ, ∃ R : ℝ, ∀ u : E n, u ∈ Dirichlet Γ →
      (∀ ξ ∈ parFixed Γ, Y ≤ busemann ξ u) → hdist (0 : E n) u ≤ R)
    (hcusp : CuspTorsionBound Γ) : BoundedTorsion Γ := by
  obtain ⟨ε₀, hε₀pos, hMε₀⟩ := hM 0
  obtain ⟨b₂, hb₂⟩ := hcusp
  obtain ⟨K, hKc, hK⟩ :=
    bt_not_thinParabolic_cocompact n hn hA hI Γ hΓ ε₀ hε₀pos (hdeep ε₀ hε₀pos) hdir
  obtain ⟨b₁, hb₁⟩ := card_le_of_fix_near_compact hA hI Γ hΓ.1 K hKc
  refine ⟨max b₁ b₂ + 1, ?_⟩
  intro F hFG hFfin
  rcases Subgroup.bot_or_exists_ne_one F with hbot | ⟨φ, hφF, hφne⟩
  · rw [hbot]
    rw [show Nat.card ↥(⊥ : Subgroup (PO n 1)) = 1 from Subgroup.card_bot]
    omega
  · obtain ⟨p, hpfix⟩ := fixPoint_of_finite hA F hFfin
    by_cases hcocomp : ∃ γ : Γ, ((γ : Γ) : PO n 1) • p ∈ K
    · obtain ⟨γ, hγK⟩ := hcocomp
      have hle := hb₁ F hFG hFfin p hpfix ⟨(γ : PO n 1), γ.2, hγK⟩
      omega
    · -- `p` is parabolically thin: a parabolic is `ε₀`-short at `p`
      have hthin : p ∈ ThinParabolic Γ ε₀ := by
        by_contra hc
        obtain ⟨γ, hγ⟩ := hK p hc
        exact hcocomp ⟨γ, hγ⟩
      obtain ⟨q, hqpar, hqshort⟩ := hthin
      obtain ⟨ξ, hξSph, hqfix⟩ :=
        (geomFiniteParabolicClass n (by omega) hA hI (q : PO n 1) hqpar).1
      have hξpar : ξ ∈ parFixed Γ := ⟨hξSph, ⟨q, hqpar, hqfix⟩⟩
      -- `hM` with `R = 0`: every element of `Γ` fixing `p` fixes `ξ`
      have hFix : ∀ f ∈ F, bd f ξ = ξ := by
        intro f hf
        have hfp : hdist p ((f : PO n 1) • p) = 0 := by
          rw [hpfix f hf, hI.2.2.1 p p]
        exact hMε₀ Γ hΓ.1 p ξ q ⟨f, hFG hf⟩ hqpar hξSph hqfix hqshort (le_of_eq hfp)
      have hle := hb₂ ξ hξpar F hFG hFfin hFix
      omega

end

end Work.Mostow
