import Mathlib
import Submission.Work.NN.Final.flatTwoTunable

namespace Work.NN.Final

noncomputable section
open scoped NNReal ENNReal ContDiff
open Set
open Work.CR.Flat

set_option maxHeartbeats 4000000

/-- The linear subspace of `(0,2)`-form families on which the tunable `(0,2)`-solver is defined:
families that are `C¹` on the polydisc `pd n ρ c`, antisymmetric there and `∂̄`-closed there. -/
def flatTwoC1Sub {n : ℕ} (ρ : Fin n → ℝ) (c : ℝ) :
    Submodule ℝ (Fin n → Fin n → Work.NN.Core.Cn n → ℂ) where
  carrier := {η | (∀ i l, ContDiffOn ℝ (1 : ℕ∞) (η i l) (pd n ρ c)) ∧
    (∀ i l z, z ∈ pd n ρ c → η i l z = -η l i z) ∧ Clos2 n ρ c η}
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · intro i l; exact contDiffOn_const
    · intro i l z hz; simp
    · intro j l m z hz; simp [Work.CR.Flat.dbarCoord]
  add_mem' := by
    intro f g hf hg
    refine ⟨?_, ?_, ?_⟩
    · intro i l; exact (hf.1 i l).add (hg.1 i l)
    · intro i l z hz
      have h1 := hf.2.1 i l z hz
      have h2 := hg.2.1 i l z hz
      simp only [Pi.add_apply]; rw [h1, h2]; ring
    · intro j l m z hz
      have df : DifferentiableAt ℝ (f l m) z :=
        ((hf.1 l m).contDiffAt ((isOpen_pd ρ c).mem_nhds hz)).differentiableAt (by norm_num)
      have dg : DifferentiableAt ℝ (g l m) z :=
        ((hg.1 l m).contDiffAt ((isOpen_pd ρ c).mem_nhds hz)).differentiableAt (by norm_num)
      have djf : DifferentiableAt ℝ (f j m) z :=
        ((hf.1 j m).contDiffAt ((isOpen_pd ρ c).mem_nhds hz)).differentiableAt (by norm_num)
      have djg : DifferentiableAt ℝ (g j m) z :=
        ((hg.1 j m).contDiffAt ((isOpen_pd ρ c).mem_nhds hz)).differentiableAt (by norm_num)
      have dlf : DifferentiableAt ℝ (f j l) z :=
        ((hf.1 j l).contDiffAt ((isOpen_pd ρ c).mem_nhds hz)).differentiableAt (by norm_num)
      have dlg : DifferentiableAt ℝ (g j l) z :=
        ((hg.1 j l).contDiffAt ((isOpen_pd ρ c).mem_nhds hz)).differentiableAt (by norm_num)
      have e1 := Work.NN.Assemble.FT.dbarCoord_add_pi (n := n) j df dg
      have e2 := Work.NN.Assemble.FT.dbarCoord_add_pi (n := n) l djf djg
      have e3 := Work.NN.Assemble.FT.dbarCoord_add_pi (n := n) m dlf dlg
      have h1 := hf.2.2 j l m z hz
      have h2 := hg.2.2 j l m z hz
      rw [show (f+g) l m = f l m + g l m from rfl, e1,
          show (f+g) j m = f j m + g j m from rfl, e2,
          show (f+g) j l = f j l + g j l from rfl, e3]
      linear_combination h1 + h2
  smul_mem' := by
    intro t f hf
    refine ⟨?_, ?_, ?_⟩
    · intro i l; exact ContDiffOn.const_smul t (hf.1 i l)
    · intro i l z hz
      have h1 := hf.2.1 i l z hz
      simp only [Pi.smul_apply, Complex.real_smul]; rw [h1]; ring
    · intro j l m z hz
      have df : DifferentiableAt ℝ (f l m) z :=
        ((hf.1 l m).contDiffAt ((isOpen_pd ρ c).mem_nhds hz)).differentiableAt (by norm_num)
      have djf : DifferentiableAt ℝ (f j m) z :=
        ((hf.1 j m).contDiffAt ((isOpen_pd ρ c).mem_nhds hz)).differentiableAt (by norm_num)
      have dlf : DifferentiableAt ℝ (f j l) z :=
        ((hf.1 j l).contDiffAt ((isOpen_pd ρ c).mem_nhds hz)).differentiableAt (by norm_num)
      have e1 := Work.NN.Final.dbarCoord_const_mul (n := n) (j := j) (t:ℂ) (f l m) z df
      have e2 := Work.NN.Final.dbarCoord_const_mul (n := n) (j := l) (t:ℂ) (f j m) z djf
      have e3 := Work.NN.Final.dbarCoord_const_mul (n := n) (j := m) (t:ℂ) (f j l) z dlf
      have h1 := hf.2.2 j l m z hz
      have hsm1 : (t • f) l m = fun w => (t:ℂ) * f l m w := by
        funext w; simp only [Pi.smul_apply, Complex.real_smul]
      have hsm2 : (t • f) j m = fun w => (t:ℂ) * f j m w := by
        funext w; simp only [Pi.smul_apply, Complex.real_smul]
      have hsm3 : (t • f) j l = fun w => (t:ℂ) * f j l w := by
        funext w; simp only [Pi.smul_apply, Complex.real_smul]
      rw [hsm1, e1, hsm2, e2, hsm3, e3]
      linear_combination (t:ℂ) * h1

theorem flatTwoTunableLinear {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {c : ℝ} (hc : 1 < c) : ∃ (T2 : (Fin n → Fin n → Work.NN.Core.Cn n → ℂ) →ₗ[ℝ] (Fin n → Work.NN.Core.Cn n → ℂ)) (C : ℝ), 0 < C ∧ (∀ η : Fin n → Fin n → Work.NN.Core.Cn n → ℂ, (∀ j l, ContDiffOn ℝ (1 : ℕ∞) (η j l) (Work.CR.Flat.polydisc 0 (fun i => c * ρ i))) → (∀ j l z, z ∈ Work.CR.Flat.polydisc 0 (fun i => c * ρ i) → η j l z = - η l j z) → Work.NN.Final.Clos2 n ρ c η → ∀ (j l : Fin n) (z : Work.NN.Core.Cn n), z ∈ Work.CR.Flat.polydisc 0 ρ → Work.CR.Flat.dbarCoord j (T2 η l) z - Work.CR.Flat.dbarCoord l (T2 η j) z = η j l z) ∧ (∀ η : Fin n → Fin n → Work.NN.Core.Cn n → ℂ, (∀ j l, ContDiffOn ℝ (1 : ℕ∞) (η j l) (Work.CR.Flat.polydisc 0 (fun i => c * ρ i))) → (∀ j l z, z ∈ Work.CR.Flat.polydisc 0 (fun i => c * ρ i) → η j l z = - η l j z) → Work.NN.Final.Clos2 n ρ c η → ∀ j : Fin n, Work.CR.Flat.holderNorm 1 α (T2 η j) (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal C * ∑ j, ∑ l, Work.CR.Flat.holderNorm 0 α (η j l) (Work.CR.Flat.polydisc 0 (fun i => c * ρ i))) := by
  by_cases hn1 : n = 1
  · subst hn1
    refine ⟨0, 1, one_pos, ?_, ?_⟩
    · intro η hη hanti hcl j l z hz
      have hjl : j = l := Subsingleton.elim j l
      have h0 : η j l z = 0 := by
        rw [hjl]
        have hmem : z ∈ Work.CR.Flat.polydisc (0 : Fin 1 → ℂ) (fun i => c * ρ i) := by
          rw [tun_mem_polydisc_zero]
          intro i
          rw [tun_mem_polydisc_zero] at hz
          have hp := hρ i
          have h := hz i
          nlinarith [h, hp, hc]
        have h := hanti l l z hmem
        linear_combination (1 / 2 : ℂ) * h
      rw [h0]
      simp [Work.CR.Flat.dbarCoord]
    · intro η hη hanti hcl j
      have hz0 : Work.CR.Flat.holderNorm 1 α (((0 : (Fin 1 → Fin 1 → Work.NN.Core.Cn 1 → ℂ) →ₗ[ℝ]
          (Fin 1 → Work.NN.Core.Cn 1 → ℂ)) η) j)
          (Work.CR.Flat.polydisc (0 : Fin 1 → ℂ) ρ) = 0 := by
        simp [Work.CR.Flat.holderNorm, Work.CR.Flat.iterDerivNorm, Work.CR.Flat.holderSeminorm]
      rw [hz0]
      exact bot_le
  · have hρc : ∀ j, 0 < c * ρ j := fun j => by have h := hρ j; nlinarith
    set c₂ : ℝ := (1 + c) / 2 with hc₂def
    set c₁ : ℝ := (1 + c₂) / 2 with hc₁def
    have hc₁1 : 1 < c₁ := by rw [hc₁def, hc₂def]; linarith
    have hc₁c₂ : c₁ < c₂ := by rw [hc₁def]; linarith
    have hc₂c : c₂ < c := by rw [hc₂def]; linarith
    have hρ₂ : ∀ j, 0 < c₂ * ρ j := fun j => by have h := hρ j; nlinarith
    have hρ₁ : ∀ j, 0 < c₁ * ρ j := fun j => by have h := hρ j; nlinarith
    have hKc : IsCompact (Set.univ.pi fun i => Metric.closedBall (0 : ℂ) (c₁ * ρ i)) :=
      isCompact_univ_pi fun i => isCompact_closedBall 0 _
    have hKU : (Set.univ.pi fun i => Metric.closedBall (0 : ℂ) (c₁ * ρ i)) ⊆ pd n ρ c₂ := by
      intro z hz
      rw [mem_pd]
      intro i
      have h := hz i
      rw [Metric.mem_closedBall, dist_eq_norm] at h
      have h1 : ‖z i‖ ≤ c₁ * ρ i := by simpa using h
      have h2 : c₁ * ρ i < c₂ * ρ i := by have hp := hρ i; nlinarith
      linarith
    obtain ⟨χ, V, hχ, hcs, htsupp, hVo, hKV, hχ1⟩ :=
      Work.NN.Core.exists_contDiff_bump_of_isCompact_subset hKc (isOpen_pd ρ c₂) hKU
    have htsuppc : tsupport χ ⊆ pd n ρ c := htsupp.trans (pd_mono hρ (le_of_lt hc₂c))
    obtain ⟨T, CT, hCTpos, hTsol, hTest, hTsm, hTreg⟩ :=
      Work.NN.Core.exists_telTwoDF_smooth (n := n) (α := α) hα0 hα1
        (ρ := fun i => c₁ * ρ i) (ρ' := ρ) hρ₁ hρ (fun i => by have h := hρ i; nlinarith)
    obtain ⟨Cb, hCbpos, hCb⟩ := Work.NN.Core.bmRow_holder (n := n) hn hα0 hα1
      (c := 0) (r := fun i => (2 * c) * ρ i) (fun i => by have h := hρ i; nlinarith) 0
    obtain ⟨Cc, hCcpos, hCc⟩ := tun_chiMul (α := α) (r := fun i => c₂ * ρ i)
      (R := fun i => c * ρ i) hα0.le hα1.le (fun i => by have h := hρ i; nlinarith)
      hχ hcs htsupp 0
    obtain ⟨Ce, hCepos, hCe⟩ := tun_Edat_gain (n := n) hn hα0 hα1 (r := fun i => c₂ * ρ i)
      (R := fun i => c * ρ i) (T := fun i => c₁ * ρ i) hρc (fun i => by have h := hρ i; nlinarith)
      (fun i => by have h := hρ i; nlinarith) hχ hcs htsupp
    have hCpos : 0 < Cb * Cc + CT 1 * ((n : ℝ) * ((n : ℝ) * Ce)) + 1 := by
      have h1 := hCbpos; have h2 := hCcpos; have h3 := hCTpos 1; have h4 := hCepos
      have h5 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      positivity
    -- Linearity of the explicit solver on the `C¹`, antisymmetric, closed subspace.
    have key_add : ∀ (u v : Fin n → Fin n → Work.NN.Core.Cn n → ℂ),
        u ∈ flatTwoC1Sub ρ c → v ∈ flatTwoC1Sub ρ c →
        Work.NN.Core.bmRow (fun a b w => χ w * (u + v) a b w)
            + T (Work.NN.Assemble.FT.Edat χ (u + v))
          = (Work.NN.Core.bmRow (fun a b w => χ w * u a b w)
              + T (Work.NN.Assemble.FT.Edat χ u))
            + (Work.NN.Core.bmRow (fun a b w => χ w * v a b w)
              + T (Work.NN.Assemble.FT.Edat χ v)) := by
      intro u v hu hv
      have hu1 := hu.1; have hv1 := hv.1
      have hrow : Work.NN.Core.bmRow (fun a b w => χ w * (u + v) a b w)
          = Work.NN.Core.bmRow (fun a b w => χ w * u a b w)
            + Work.NN.Core.bmRow (fun a b w => χ w * v a b w) := by
        funext i z
        have hcu : ∀ l : Fin n, Continuous (fun w => χ w * u i l w) := fun l =>
          (contDiff_mul_of_contDiffOn_tsupport (m := 1) (isOpen_pd ρ c) hχ htsuppc (hu1 i l)).continuous
        have hcv : ∀ l : Fin n, Continuous (fun w => χ w * v i l w) := fun l =>
          (contDiff_mul_of_contDiffOn_tsupport (m := 1) (isOpen_pd ρ c) hχ htsuppc (hv1 i l)).continuous
        have hsu : ∀ l : Fin n, HasCompactSupport (fun w => χ w * u i l w) := fun l => hcs.mul_right
        have hsv : ∀ l : Fin n, HasCompactSupport (fun w => χ w * v i l w) := fun l => hcs.mul_right
        have hfam : (fun l : Fin n => fun w => χ w * u i l w + χ w * v i l w)
            = fun l => fun w => χ w * (u i l w + v i l w) := by
          funext l w; ring
        simp only [Work.NN.Core.bmRow_apply, Pi.add_apply]
        rw [← hfam, congrFun (Work.NN.Core.bmPot_add' hn (f := fun l w => χ w * u i l w)
              (g := fun l w => χ w * v i l w) hcu hcv hsu hsv) z]
        simp only [Pi.add_apply]; ring
      have hedat : Work.NN.Assemble.FT.Edat χ (u + v)
          = Work.NN.Assemble.FT.Edat χ u + Work.NN.Assemble.FT.Edat χ v := by
        funext i m z
        have hcu : ∀ k : Fin n, Continuous (fun w => Work.NN.Core.bmH χ u i m k w) := fun k =>
          (tun_contDiff_bmH hχ htsuppc hu1 i m k).continuous
        have hcv : ∀ k : Fin n, Continuous (fun w => Work.NN.Core.bmH χ v i m k w) := fun k =>
          (tun_contDiff_bmH hχ htsuppc hv1 i m k).continuous
        have hsu : ∀ k : Fin n, HasCompactSupport (fun w => Work.NN.Core.bmH χ u i m k w) := fun k =>
          Work.NN.Core.hasCompactSupport_bmH' hcs u i m k
        have hsv : ∀ k : Fin n, HasCompactSupport (fun w => Work.NN.Core.bmH χ v i m k w) := fun k =>
          Work.NN.Core.hasCompactSupport_bmH' hcs v i m k
        have hfam : (fun k : Fin n => fun w => Work.NN.Core.bmH χ u i m k w
              + Work.NN.Core.bmH χ v i m k w)
            = fun k => fun w => Work.NN.Core.bmH χ (u + v) i m k w := by
          funext k w; rw [Work.NN.Core.bmH_add' χ u v i m k w]
        simp only [Work.NN.Assemble.FT.Edat_apply, Pi.add_apply]
        rw [← hfam, congrFun (Work.NN.Core.bmPot_add' hn (f := fun k w => Work.NN.Core.bmH χ u i m k w)
              (g := fun k w => Work.NN.Core.bmH χ v i m k w) hcu hcv hsu hsv) z]
        simp only [Pi.add_apply]; ring
      rw [hrow, hedat, map_add]
      abel
    have key_smul : ∀ (t : ℝ) (u : Fin n → Fin n → Work.NN.Core.Cn n → ℂ), u ∈ flatTwoC1Sub ρ c →
        Work.NN.Core.bmRow (fun a b w => χ w * (t • u) a b w)
            + T (Work.NN.Assemble.FT.Edat χ (t • u))
          = t • (Work.NN.Core.bmRow (fun a b w => χ w * u a b w)
              + T (Work.NN.Assemble.FT.Edat χ u)) := by
      intro t u hu
      have hu1 := hu.1
      have hrow : Work.NN.Core.bmRow (fun a b w => χ w * (t • u) a b w)
          = t • Work.NN.Core.bmRow (fun a b w => χ w * u a b w) := by
        funext i z
        have hcu : ∀ l : Fin n, Continuous (fun w => χ w * u i l w) := fun l =>
          (contDiff_mul_of_contDiffOn_tsupport (m := 1) (isOpen_pd ρ c) hχ htsuppc (hu1 i l)).continuous
        have hsu : ∀ l : Fin n, HasCompactSupport (fun w => χ w * u i l w) := fun l => hcs.mul_right
        have hfam : (fun l : Fin n => fun w => (t:ℂ) * (χ w * u i l w))
            = fun l => fun w => χ w * (t • u) i l w := by
          funext l w; simp only [Pi.smul_apply, Complex.real_smul]; ring
        have hsmv : (t • Work.NN.Core.bmRow (fun a b w => χ w * u a b w)) i z
            = t • (Work.NN.Core.bmRow (fun a b w => χ w * u a b w) i z) := by
          simp only [Pi.smul_apply]
        rw [hsmv, Work.NN.Core.bmRow_apply, Work.NN.Core.bmRow_apply, ← hfam,
            congrFun (Work.NN.Core.bmPot_real_smul' hn t hcu hsu) z]
        simp only [Pi.smul_apply, Complex.real_smul]; ring
      have hedat : Work.NN.Assemble.FT.Edat χ (t • u)
          = t • Work.NN.Assemble.FT.Edat χ u := by
        funext i m z
        have hcu : ∀ k : Fin n, Continuous (fun w => Work.NN.Core.bmH χ u i m k w) := fun k =>
          (tun_contDiff_bmH hχ htsuppc hu1 i m k).continuous
        have hsu : ∀ k : Fin n, HasCompactSupport (fun w => Work.NN.Core.bmH χ u i m k w) := fun k =>
          Work.NN.Core.hasCompactSupport_bmH' hcs u i m k
        have hfam : (fun k : Fin n => fun w => (t:ℂ) * Work.NN.Core.bmH χ u i m k w)
            = fun k => fun w => Work.NN.Core.bmH χ (t • u) i m k w := by
          funext k w; rw [Work.NN.Core.bmH_smul' χ t u i m k w, Complex.real_smul]
        have hsmv : (t • Work.NN.Assemble.FT.Edat χ u) i m z
            = t • (Work.NN.Assemble.FT.Edat χ u i m z) := by
          simp only [Pi.smul_apply]
        rw [hsmv, Work.NN.Assemble.FT.Edat_apply, Work.NN.Assemble.FT.Edat_apply, ← hfam,
            congrFun (Work.NN.Core.bmPot_real_smul' hn t hcu hsu) z]
        simp only [Pi.smul_apply, Complex.real_smul]; ring
      rw [hrow, hedat, map_smul]
      rw [smul_add]
    let S : flatTwoC1Sub ρ c →ₗ[ℝ] (Fin n → Work.NN.Core.Cn n → ℂ) :=
      { toFun := fun x => Work.NN.Core.bmRow
            (fun a b w => χ w * (x : Fin n → Fin n → Work.NN.Core.Cn n → ℂ) a b w)
          + T (Work.NN.Assemble.FT.Edat χ (x : Fin n → Fin n → Work.NN.Core.Cn n → ℂ))
        map_add' := fun x y => by
          have h := key_add x.1 y.1 x.2 y.2
          simpa only [Submodule.coe_add] using h
        map_smul' := fun t x => by
          have h := key_smul t x.1 x.2
          simpa only [Submodule.coe_smul, RingHom.id_apply] using h }
    obtain ⟨T2, hT2raw⟩ := LinearMap.exists_extend S
    have hT2η : ∀ (η : Fin n → Fin n → Work.NN.Core.Cn n → ℂ) (h : η ∈ flatTwoC1Sub ρ c),
        T2 η = Work.NN.Core.bmRow (fun a b w => χ w * η a b w)
          + T (Work.NN.Assemble.FT.Edat χ η) := by
      intro η h
      have hpt : T2 η = S ⟨η, h⟩ := congrFun (congrArg DFunLike.coe hT2raw) (⟨η, h⟩ : flatTwoC1Sub ρ c)
      rw [show S ⟨η, h⟩ = Work.NN.Core.bmRow (fun a b w => χ w * η a b w)
            + T (Work.NN.Assemble.FT.Edat χ η) from rfl] at hpt
      exact hpt
    refine ⟨T2, Cb * Cc + CT 1 * ((n : ℝ) * ((n : ℝ) * Ce)) + 1, hCpos, ?_, ?_⟩
    · -- the equation
      intro η hη hanti hcl j l z hz
      have hg := hT2η η (show η ∈ flatTwoC1Sub ρ c from ⟨hη, hanti, hcl⟩)
      rw [hg]
      show Work.CR.Flat.dbarCoord j (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) l
            + T (Work.NN.Assemble.FT.Edat χ η) l) z
          - Work.CR.Flat.dbarCoord l (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j
            + T (Work.NN.Assemble.FT.Edat χ η) j) z = η j l z
      have hη' : ∀ i m, ContDiffOn ℝ 1 (η i m) (pd n ρ c) := fun i m => hη i m
      have hcl' : ∀ i m m' w, w ∈ pd n ρ c →
          dbarCoord i (η m m') w - dbarCoord m (η i m') w
            + dbarCoord m' (η i m) w = 0 := fun i m m' w hw => hcl i m m' w hw
      have hKV1 : Set.univ.pi (fun i => Metric.closedBall (0 : ℂ) (ρ i)) ⊆ V := by
        intro z hz2
        refine hKV ?_
        rw [Set.mem_univ_pi] at hz2 ⊢
        intro i
        have h := hz2 i
        rw [Metric.mem_closedBall, dist_eq_norm] at h ⊢
        have h1 : ‖z i‖ ≤ ρ i := by simpa using h
        have h2 : ρ i ≤ c₁ * ρ i := by have hp := hρ i; nlinarith
        simpa using le_trans h1 h2
      have hdef := tun_bmDefect (n := n) hn (r := fun i => c₂ * ρ i) (r₁ := ρ)
        (R := fun i => c * ρ i) hρc (fun i => by have h := hρ i; nlinarith)
        (fun i => by have h := hρ i; nlinarith) hχ hcs htsupp hVo hKV1 hχ1 hη' hcl' j l z hz
      have hEd1 : ∀ i m : Fin n,
          ContDiffOn ℝ 1 (Work.NN.Assemble.FT.Edat χ η i m)
            (polydisc 0 (fun i => c₁ * ρ i)) :=
        fun i m => (tun_Edat_contDiff hn hχ hcs htsuppc hη' i m).contDiffOn
      have hEanti : Work.NN.Core.IsAntisymmTwo (Work.NN.Assemble.FT.Edat χ η) :=
        fun i m w => tun_Edat_antisymm hn hχ hcs htsuppc hη' hanti i m w
      have hEcl : Work.NN.Core.IsClosedTwoOn (fun i => c₁ * ρ i)
          (Work.NN.Assemble.FT.Edat χ η) :=
        fun i m m' w hw => tun_Edat_closed hn (r := fun i => c₂ * ρ i) (R := fun i => c * ρ i)
          (S := fun i => c₁ * ρ i) (fun j => le_of_lt (by have h := hρ j; nlinarith))
          (fun j => by have h := hρ j; nlinarith) hχ hcs htsupp hVo hKV hχ1 hη' hcl' i m m' w hw
      have hTs := hTsol (Work.NN.Assemble.FT.Edat χ η) hEd1 hEanti hEcl j l z hz
      have hbm : Work.NN.Core.bmDefect χ η j l z = - Work.NN.Assemble.FT.Edat χ η j l z := by
        rw [Work.NN.Core.bmDefect_apply, Work.NN.Assemble.FT.Edat_apply]
        have hχz : χ z = 1 := hχ1 z (hKV (by
          rw [Set.mem_univ_pi]
          intro i
          rw [Metric.mem_closedBall, dist_zero_right]
          rw [tun_mem_polydisc_zero] at hz
          have h := hz i
          have h2 : ρ i ≤ c₁ * ρ i := by have hp := hρ i; nlinarith
          linarith))
        rw [hχz]; ring
      have hglob : ∀ a b : Fin n, ContDiff ℝ 1 (fun w => χ w * η a b w) := fun a b =>
        Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport (m := 1) (isOpen_pd ρ c) hχ htsuppc
          (hη' a b)
      have hAd : ∀ i : Fin n, DifferentiableAt ℝ
          (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) i) z := fun i =>
        Work.NN.Assemble.FT.differentiableAt_bmRow hn
          (fun a b => hglob a b) (fun a b => hcs.mul_right) i z
      have hTd : ∀ i : Fin n, DifferentiableAt ℝ (T (Work.NN.Assemble.FT.Edat χ η) i) z :=
        fun i => ((hTreg 1 (Work.NN.Assemble.FT.Edat χ η) hEd1 i).contDiffAt
          ((isOpen_polydisc (0 : Fin n → ℂ) ρ).mem_nhds hz)).differentiableAt one_ne_zero
      rw [hbm] at hdef
      rw [Work.NN.Assemble.FT.dbarCoord_add_pi j (hAd l) (hTd l),
          Work.NN.Assemble.FT.dbarCoord_add_pi l (hAd j) (hTd j)]
      linear_combination hdef + hTs
    · -- the estimate
      intro η hη hanti hcl j
      have hg := hT2η η (show η ∈ flatTwoC1Sub ρ c from ⟨hη, hanti, hcl⟩)
      rw [hg]
      have hη' : ∀ i m, ContDiffOn ℝ 1 (η i m) (pd n ρ c) := fun i m => hη i m
      have hcl' : ∀ i m m' w, w ∈ pd n ρ c →
          dbarCoord i (η m m') w - dbarCoord m (η i m') w
            + dbarCoord m' (η i m) w = 0 := fun i m m' w hw => hcl i m m' w hw
      set S' : ℝ≥0∞ := ∑ j : Fin n, ∑ l : Fin n, Work.CR.Flat.holderNorm 0 α (η j l)
        (Work.CR.Flat.polydisc 0 (fun i => c * ρ i)) with hSdef
      by_cases htop : S' = ⊤
      · rw [htop, ENNReal.mul_top (by rw [ENNReal.ofReal_ne_zero_iff]; positivity)]
        exact le_top
      · have hglob : ∀ a b : Fin n, ContDiff ℝ 1 (fun w => χ w * η a b w) := fun a b =>
          Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport (m := 1) (isOpen_pd ρ c) hχ htsuppc
            (hη' a b)
        have hEd1 : ∀ i m : Fin n,
            ContDiffOn ℝ 1 (Work.NN.Assemble.FT.Edat χ η i m)
              (polydisc 0 (fun i => c₁ * ρ i)) :=
          fun i m => (tun_Edat_contDiff hn hχ hcs htsuppc hη' i m).contDiffOn
        have hEanti : Work.NN.Core.IsAntisymmTwo (Work.NN.Assemble.FT.Edat χ η) :=
          fun i m w => tun_Edat_antisymm hn hχ hcs htsuppc hη' hanti i m w
        have hEcl : Work.NN.Core.IsClosedTwoOn (fun i => c₁ * ρ i)
            (Work.NN.Assemble.FT.Edat χ η) :=
          fun i m m' w hw => tun_Edat_closed hn (r := fun i => c₂ * ρ i) (R := fun i => c * ρ i)
            (S := fun i => c₁ * ρ i) (fun j => le_of_lt (by have h := hρ j; nlinarith))
            (fun j => by have h := hρ j; nlinarith) hχ hcs htsupp hVo hKV hχ1 hη' hcl'
            i m m' w hw
        have hvan : ∀ a b (w : Fin n → ℂ),
            (∃ i, ((2 * c) * ρ i) / 2 ≤ ‖w i - (0 : Fin n → ℂ) i‖) → χ w * η a b w = 0 := by
          intro a b w hw
          obtain ⟨i, hi⟩ := hw
          simp only [Pi.zero_apply, sub_zero] at hi
          have hwi : c * ρ i ≤ ‖w i‖ := by linarith [hi]
          have hnot : w ∉ pd n ρ c := fun h => by
            have h1 := mem_pd.mp h i
            linarith
          have hχ0 : χ w = 0 := by
            by_contra hc0
            exact hnot (htsuppc (subset_tsupport χ (Function.mem_support.mpr hc0)))
          rw [hχ0, zero_mul]
        have hset : polydisc (0 : Fin n → ℂ) (fun i => ((2 * c) * ρ i) / 2) = pd n ρ c := by
          have hfun : (fun i : Fin n => ((2 * c) * ρ i) / 2) = fun i : Fin n => c * ρ i := by
            funext i; ring
          rw [hfun]; rfl
        have hbmEst : Work.CR.Flat.holderNorm 1 α
            (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j) (polydisc 0 ρ)
            ≤ ENNReal.ofReal (Cb * Cc) * S' := by
          have hcb := hCb (fun a b w => χ w * η a b w) (fun a b => hglob a b) hvan j
          rw [hset] at hcb
          have hsumC : (∑ m : Fin n, ∑ m' : Fin n,
                Work.CR.Flat.holderNorm 0 α (fun w => χ w * η m m' w) Set.univ)
              ≤ ENNReal.ofReal Cc * S' := by
            rw [hSdef, Finset.mul_sum]
            refine Finset.sum_le_sum fun m _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_le_sum fun m' _ => hCc (η m m') ((hη' m m').of_le (by norm_num))
          calc Work.CR.Flat.holderNorm 1 α
                (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j) (polydisc 0 ρ)
              ≤ Work.CR.Flat.holderNorm 1 α
                  (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j) (pd n ρ c) :=
                Work.CR.Flat.holderNorm_mono_set (isOpen_pd ρ c) (isOpen_polydisc 0 ρ)
                  (polydisc_mono (fun i => by have h := hρ i; nlinarith)) 1 α _
            _ ≤ ENNReal.ofReal Cb * (∑ m : Fin n, ∑ m' : Fin n,
                  Work.CR.Flat.holderNorm 0 α (fun w => χ w * η m m' w) Set.univ) := hcb
            _ ≤ ENNReal.ofReal Cb * (ENNReal.ofReal Cc * S') := mul_le_mul' le_rfl hsumC
            _ = ENNReal.ofReal (Cb * Cc) * S' := by
                rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hCbpos)]
        have hsumE : (∑ i : Fin n, ∑ m : Fin n,
              Work.CR.Flat.holderNorm 1 α (Work.NN.Assemble.FT.Edat χ η i m)
                (polydisc 0 (fun i => c₁ * ρ i)))
            ≤ ENNReal.ofReal ((n : ℝ) * ((n : ℝ) * Ce)) * S' := by
          have hle : (∑ i : Fin n, ∑ m : Fin n,
                Work.CR.Flat.holderNorm 1 α (Work.NN.Assemble.FT.Edat χ η i m)
                  (polydisc 0 (fun i => c₁ * ρ i)))
              ≤ ∑ _i : Fin n, ∑ _m : Fin n, (ENNReal.ofReal Ce * S') :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun m _ => by
              rw [hSdef]; exact hCe η hη' i m
          refine hle.trans (le_of_eq ?_)
          exact tun_sum_sum_ofReal_mul n (le_of_lt hCepos) S'
        have hTest' : Work.CR.Flat.holderNorm 1 α (T (Work.NN.Assemble.FT.Edat χ η) j)
              (polydisc 0 ρ)
            ≤ ENNReal.ofReal (CT 1 * ((n : ℝ) * ((n : ℝ) * Ce))) * S' := by
          have ht := hTest 1 (Work.NN.Assemble.FT.Edat χ η) hEd1 hEanti hEcl j
          calc Work.CR.Flat.holderNorm 1 α (T (Work.NN.Assemble.FT.Edat χ η) j) (polydisc 0 ρ)
              ≤ ENNReal.ofReal (CT 1) * (∑ i : Fin n, ∑ m : Fin n,
                  Work.CR.Flat.holderNorm 1 α (Work.NN.Assemble.FT.Edat χ η i m)
                    (polydisc 0 (fun i => c₁ * ρ i))) := ht
            _ ≤ ENNReal.ofReal (CT 1)
                  * (ENNReal.ofReal ((n : ℝ) * ((n : ℝ) * Ce)) * S') :=
                mul_le_mul' le_rfl hsumE
            _ = ENNReal.ofReal (CT 1 * ((n : ℝ) * ((n : ℝ) * Ce))) * S' := by
                rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (hCTpos 1))]
        have hsplit := Work.CR.Flat.Holder.holderNorm_add_le
          (f := Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j)
          (g := T (Work.NN.Assemble.FT.Edat χ η) j)
          (Ω := polydisc 0 ρ) (α := α)
          (Work.NN.Assemble.FT.contDiff_bmRow hn (fun a b => hglob a b)
            (fun a b => hcs.mul_right) j).contDiffOn
          (hTreg 1 (Work.NN.Assemble.FT.Edat χ η) hEd1 j)
          (isOpen_polydisc (0 : Fin n → ℂ) ρ).uniqueDiffOn
        have harith : ENNReal.ofReal (Cb * Cc) * S'
              + ENNReal.ofReal (CT 1 * ((n : ℝ) * ((n : ℝ) * Ce))) * S'
            = ENNReal.ofReal (Cb * Cc + CT 1 * ((n : ℝ) * ((n : ℝ) * Ce))) * S' := by
          have g1 : (0 : ℝ) ≤ Cb * Cc := le_of_lt (mul_pos hCbpos hCcpos)
          have g2 : (0 : ℝ) ≤ CT 1 * ((n : ℝ) * ((n : ℝ) * Ce)) :=
            mul_nonneg (le_of_lt (hCTpos 1))
              (mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (Nat.cast_nonneg n) (le_of_lt hCepos)))
          rw [← add_mul, ← ENNReal.ofReal_add g1 g2]
        refine (hsplit.trans (add_le_add hbmEst hTest')).trans ?_
        rw [harith]
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (bot_le)
        linarith [le_of_lt (hCTpos 1)]

end

end Work.NN.Final
