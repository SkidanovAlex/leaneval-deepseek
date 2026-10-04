import Mathlib
import Submission.Work.Diff.STE.deTurck.pPhi_decomp
import Submission.Work.Diff.STE.fill.matInv_entry_bound
import Submission.Work.Diff.STE.DeTurckJet
import Submission.Work.Diff.EXT.ricJetDefs
import Submission.Work.Diff.STE.Lead.pPhi_chain
import Submission.Work.Diff.STE.Lead.jInv_entry_le_inv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.Lead

open Work.Diff.EXT Work.Diff.STE.DeTurck

/-
This is exactly the statement of `Work.Diff.STE.Lead.pPhi_entry_bound` (approved by both reviewers),
re-requested at a new path because the file at the old path was created with a placeholder identifier
(`Abar_placeholder`) in the conclusion, which under `autoImplicit` became a free variable and made the
statement unprovable.  No mathematical change.

`Work.Diff.STE.DeTurck.pPhi = -2 * jRic + jLW` (see `Submission/Work/Diff/STE/DeTurckJet.lean`) is a
sum of products of the entries of the jet data, with the only nonlinear ingredient being the inverse
Gram matrix `jInv A = (Matrix.of A)⁻¹`.  Every evaluation is on the canonical basis `bB`.

The three constants play different roles: `MA` bounds the *value* `A` of the metric's Gram matrix,
`MB` bounds the whole *background* jet `(Abar, Lbar, Bbar)` and `M` bounds the *foreground* first and
second jets `L`, `B`.  In the intended application `MA` and `MB` are FIXED constants while only `M`
grows with the composite norm.

Estimate from the inside out, using `1 ≤ MA`, `1 ≤ MB`, `1 ≤ M`, `0 < cl ≤ 1`:
* `|jInv A r s| ≤ 1 / cl` and `|jInv Abar r s| ≤ 1 / cl` from the quadratic-form lower bounds, via
  `Work.Diff.STE.fill.matInv_entry_bound` (which needs only the quadratic-form bound, not symmetry);
* the entry bounds (`‖L (bB k)‖ ≤ ...` bounds every entry of the matrix `L (bB k)`, the norm on
  `MatE = Fin n → Fin n → ℝ` being the sup norm);
* `jKz`, `jKzD`, `jGamU`, `jdInv`, `jdGamU` are of degree ≤ 1 in the foreground jets and ≤ 1 in the
  background (`jdGamU` degree ≤ 2), and `jWU`, `jWb`, `jdWU`, `jdWb`, `jnabW`, `jLW`, `jRm`, `jRic`
  are of degree ≤ 2 in the foreground derivative jet `(L,B)` and ≤ 2 in the background jet, so
  `|pPhi| ≤ const * (1 + M) ^ 2 * (1 + MA) ^ 2 * (1 + MB) ^ 2 / cl ^ 5`.
-/

theorem pPhi_entry_bound_v2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Abar : Work.Diff.EXT.MatE (E := E))
      (Lbar : Work.Diff.STE.DeTurck.LinMat E) (Bbar : Work.Diff.STE.DeTurck.BilMat E)
      (A : Work.Diff.EXT.MatE (E := E)) (L : Work.Diff.STE.DeTurck.LinMat E)
      (B : Work.Diff.STE.DeTurck.BilMat E) (MA MB M cl : ℝ) (i j : Fin (Module.finrank ℝ E)),
      1 ≤ MA → 1 ≤ MB → 1 ≤ M → 0 < cl → cl ≤ 1 →
      (∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
        cl * ∑ k, (ξ k) ^ 2 ≤ ∑ k, ∑ l, A k l * ξ k * ξ l) →
      (∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
        cl * ∑ k, (ξ k) ^ 2 ≤ ∑ k, ∑ l, Abar k l * ξ k * ξ l) →
      (∀ k l, |A k l| ≤ MA) → (∀ k l, |Abar k l| ≤ MB) →
      (∀ k : Fin (Module.finrank ℝ E), ‖L (Work.Diff.EXT.bB (E := E) k)‖ ≤ M) →
      (∀ k : Fin (Module.finrank ℝ E), ‖Lbar (Work.Diff.EXT.bB (E := E) k)‖ ≤ MB) →
      (∀ k l : Fin (Module.finrank ℝ E),
        ‖B (Work.Diff.EXT.bB (E := E) k) (Work.Diff.EXT.bB (E := E) l)‖ ≤ M) →
      (∀ k l : Fin (Module.finrank ℝ E),
        ‖Bbar (Work.Diff.EXT.bB (E := E) k) (Work.Diff.EXT.bB (E := E) l)‖ ≤ MB) →
      |Work.Diff.STE.DeTurck.pPhi Abar Lbar Bbar A L B i j|
        ≤ C * (1 + M) ^ 2 * (1 + MA) ^ 2 * (1 + MB) ^ 2 / cl ^ 5 := by
  by_cases hn : 1 ≤ Module.finrank ℝ E
  · -- the constant of the bound, assembled from the chain of `pPhi_chain.lean`
    have hkc : 0 ≤ idxCard E := by simp only [idxCard]; positivity
    let kKz : ℝ := 3 * 1
    have hkKznn : 0 ≤ kKz := by positivity
    let kGam : ℝ := idxCard E * (1 * kKz)
    have hkGamnn : 0 ≤ kGam := by positivity
    let kJdInv : ℝ := idxCard E * (idxCard E * (1 * 1 * 1))
    have hkJdInvnn : 0 ≤ kJdInv := by positivity
    let kJdGam : ℝ := idxCard E * (kJdInv * kKz + 1 * kKz)
    have hkJdGamnn : 0 ≤ kJdGam := by positivity
    let kRm : ℝ := ((kKz + kKz) + idxCard E * (idxCard E * (1 * kKz * kKz)))
      + idxCard E * (idxCard E * (1 * kKz * kKz))
    have hkRmnn : 0 ≤ kRm := by positivity
    let kRic : ℝ := idxCard E * (idxCard E * (1 * kRm))
    have hkRicnn : 0 ≤ kRic := by positivity
    let kWU : ℝ := idxCard E * (idxCard E * (1 * (kGam + kGam)))
    have hkWUnn : 0 ≤ kWU := by positivity
    let kWb : ℝ := idxCard E * (1 * kWU)
    have hkWbnn : 0 ≤ kWb := by positivity
    let kJdWU : ℝ := idxCard E * (idxCard E * ((kJdInv * (kGam + kGam) + 1 * kJdGam) + 1 * kJdGam))
    have hkJdWUnn : 0 ≤ kJdWU := by positivity
    let kJdWb : ℝ := idxCard E * (1 * kWU + 1 * kJdWU)
    have hkJdWbnn : 0 ≤ kJdWb := by positivity
    let kNab : ℝ := kJdWb + idxCard E * (kGam * kWb)
    have hkNabnn : 0 ≤ kNab := by positivity
    let kLW : ℝ := kNab + kNab
    have hkLWnn : 0 ≤ kLW := by positivity
    let kFin : ℝ := |(-2 : ℝ)| * kRic + kLW
    have hkFinn : 0 ≤ kFin := by positivity
    refine ⟨kFin, hkFinn, ?_⟩
    intro Abar Lbar Bbar A L B MA MB M cl i j hMA hMB hM hcl hcl1 hquadA hquadAbar
      hAbound hAbarbound hLnorm hLbarnorm hBnorm hBbarnorm
    have hh : Hyp M MA MB cl := ⟨hM, hMA, hMB, hcl, hcl1⟩
    -- the atoms
    have hInvA : ∀ r s, Lv 0 0 0 1 1 M MA MB cl (jInv A r s) := by
      intro r s
      have h := jInv_entry_le_inv (A := A) hcl hquadA r s
      simpa only [Lv, pow_one, pow_zero, mul_one, one_mul] using h
    have hInvAb : ∀ r s, Lv 0 0 0 1 1 M MA MB cl (jInv Abar r s) := by
      intro r s
      have h := jInv_entry_le_inv (A := Abar) hcl hquadAbar r s
      simpa only [Lv, pow_one, pow_zero, mul_one, one_mul] using h
    have hA_E : ∀ i j, Lv 0 1 0 0 1 M MA MB cl (A i j) := Lv_entry_A hh hAbound
    have hAb_E : ∀ i j, Lv 0 0 1 0 1 M MA MB cl (Abar i j) := Lv_entry_Abar hh hAbarbound
    have hL_E : ∀ a p q, Lv 1 0 0 0 1 M MA MB cl (L (bB (E := E) a) p q) :=
      fun a => Lv_entry_fg hh (hLnorm a)
    have hLb_E : ∀ a p q, Lv 0 0 1 0 1 M MA MB cl (Lbar (bB (E := E) a) p q) :=
      fun a => Lv_entry_bg hh (hLbarnorm a)
    have hB_E : ∀ a b p q, Lv 1 0 0 0 1 M MA MB cl
        (B (bB (E := E) a) (bB (E := E) b) p q) :=
      fun a b => Lv_entry_fg hh (hBnorm a b)
    have hBb_E : ∀ a b p q, Lv 0 0 1 0 1 M MA MB cl
        (Bbar (bB (E := E) a) (bB (E := E) b) p q) :=
      fun a b => Lv_entry_bg hh (hBbarnorm a b)
    -- the chain
    have hKz : ∀ a b c, Lv 1 0 0 0 kKz M MA MB cl (jKz L a b c) :=
      chain_jKz hh (by norm_num) hL_E
    have hKzD : ∀ m a b c, Lv 1 0 0 0 kKz M MA MB cl (jKzD B m a b c) :=
      chain_jKzD hh (by norm_num) hB_E
    have hKzB : ∀ a b c, Lv 0 0 1 0 kKz M MA MB cl (jKz Lbar a b c) :=
      chain_jKz_bg hh (by norm_num) hLb_E
    have hKzDB : ∀ m a b c, Lv 0 0 1 0 kKz M MA MB cl (jKzD Bbar m a b c) :=
      chain_jKzD_bg hh (by norm_num) hBb_E
    have hGam : ∀ r a b, Lv 1 0 0 1 kGam M MA MB cl (jGamU A L r a b) :=
      chain_jGamU hh (by norm_num) hkKznn hInvA hKz
    have hGamb : ∀ r a b, Lv 0 0 1 1 kGam M MA MB cl (jGamU Abar Lbar r a b) :=
      chain_jGamU_bg hh (by norm_num) hkKznn hInvAb hKzB
    have hJdInv : ∀ a i j, Lv 1 0 0 2 kJdInv M MA MB cl (jdInv A L a i j) :=
      chain_jdInv hh (by norm_num) (by norm_num) hInvA hL_E
    have hJdInvB : ∀ a i j, Lv 0 0 1 2 kJdInv M MA MB cl (jdInv Abar Lbar a i j) :=
      chain_jdInv_bg hh (by norm_num) (by norm_num) hInvAb hLb_E
    have hJdGam : ∀ a r i j, Lv 2 0 0 2 kJdGam M MA MB cl (jdGamU A L B a r i j) :=
      chain_jdGamU hh (by norm_num) hkKznn hkKznn hkJdInvnn hInvA hKz hKzD hJdInv
    have hJdGamb : ∀ a r i j, Lv 0 0 2 2 kJdGam M MA MB cl
        (jdGamU Abar Lbar Bbar a r i j) :=
      chain_jdGamU_bg hh (by norm_num) hkKznn hkKznn hkJdInvnn hInvAb hKzB hKzDB hJdInvB
    have hRm : ∀ a b c d, Lv 2 0 0 1 kRm M MA MB cl (jRm A L B a b c d) :=
      chain_jRm hh (by norm_num) hkKznn hkKznn hInvA hKz hKzD
    have hRic : ∀ i j, Lv 2 0 0 2 kRic M MA MB cl (jRic A L B i j) :=
      chain_jRic hh (by norm_num) hkRmnn hInvA hRm
    have hWU : ∀ k, Lv 1 0 1 2 kWU M MA MB cl (jWU A L Abar Lbar k) :=
      chain_jWU hh (by norm_num) hkGamnn hkGamnn hInvA hGam hGamb
    have hWb : ∀ b, Lv 1 1 1 2 kWb M MA MB cl (jWb A L Abar Lbar b) :=
      chain_jWb hh (by norm_num) hkWUnn hA_E hWU
    have hJdWU : ∀ a c, Lv 2 0 2 3 kJdWU M MA MB cl (jdWU A L B Abar Lbar Bbar a c) :=
      chain_jdWU hh (by norm_num) hkJdInvnn hkGamnn hkGamnn hkJdGamnn hkJdGamnn
        hInvA hJdInv hGam hGamb hJdGam hJdGamb
    have hJdWb : ∀ a b, Lv 2 1 2 3 kJdWb M MA MB cl (jdWb A L B Abar Lbar Bbar a b) :=
      chain_jdWb hh (by norm_num) hkWUnn (by norm_num) hkJdWUnn hL_E hA_E hWU hJdWU
    have hNab : ∀ a b, Lv 2 1 2 3 kNab M MA MB cl (jnabW A L B Abar Lbar Bbar a b) :=
      chain_jnabW hh hkJdWbnn hkGamnn hkWbnn hJdWb hGam hWb
    have hLW : ∀ a b, Lv 2 1 2 3 kLW M MA MB cl (jLW A L B Abar Lbar Bbar a b) :=
      chain_jLW hh hkNabnn hNab
    -- assemble `pPhi`
    have hRic_i := hRic i j
    have hLW_i := hLW i j
    have hpp : Lv 2 1 2 3 kFin M MA MB cl (pPhi Abar Lbar Bbar A L B i j) := by
      have h1 : Lv 2 0 0 2 (|(-2 : ℝ)| * kRic) M MA MB cl ((-2) * jRic A L B i j) :=
        Lv.smul (-2) hRic_i
      have h2 : Lv 2 1 2 3 (|(-2 : ℝ)| * kRic + kLW) M MA MB cl
          ((-2) * jRic A L B i j + jLW A L B Abar Lbar Bbar i j) :=
        Lv.addmax h1 hLW_i hh (mul_nonneg (abs_nonneg _) hkRicnn) hkLWnn
      simpa only [pPhi] using h2
    -- convert the degrees to the shape of the statement
    have hfin : Lv 2 2 2 5 kFin M MA MB cl (pPhi Abar Lbar Bbar A L B i j) :=
      Lv.mono hpp hh hkFinn le_rfl (by omega) le_rfl (by omega)
    simp only [Lv] at hfin
    rw [div_eq_mul_inv]
    calc |pPhi Abar Lbar Bbar A L B i j|
        ≤ kFin * ((1 + M) ^ 2 * ((1 + MA) ^ 2 * ((1 + MB) ^ 2 * (cl⁻¹) ^ 5))) := hfin
      _ = kFin * (1 + M) ^ 2 * (1 + MA) ^ 2 * (1 + MB) ^ 2 * (cl ^ 5)⁻¹ := by
          rw [inv_pow]; ring
  · refine ⟨0, le_refl 0, ?_⟩
    intro Abar Lbar Bbar A L B MA MB M cl i j h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    exact absurd i.isLt (by omega)

end Work.Diff.STE.Lead
