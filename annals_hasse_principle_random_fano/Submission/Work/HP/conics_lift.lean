import Mathlib
import Submission.Work.HP.ConicsDefs
import Submission.Work.HP.ConicsLiftDefs
import Submission.Work.HP.conics_lift_fiber
import Submission.Work.HP.conics_lift_qfPhi
import Submission.Work.HP.conics_lift_indep

open Work.HP.Conics

namespace Work.HP

/-- For a sharp conic `ā` on the line `⟨v⟩`, the value of `ā` at `v` vanishes. -/
theorem qf_sharp_zero (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (ā : Mon 2 2 → ZMod p)
    (v : Fin 3 → ZMod p) (hv : SharpAt ā v) : qf ā v = 0 := by
  have h0 : pol ā v v = 0 := hv.2.1 v
  have h2 : pol ā v v = 2 * qf ā v := by
    have hvv : v + v = (2 : ZMod p) • v := by
      funext i
      show v i + v i = (2 : ZMod p) * v i
      ring
    rw [pol, hvv, qf_smul]
    ring
  rw [h2] at h0
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hc
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hc
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  exact (mul_eq_zero.mp h0).resolve_left h2ne

/-- `Work.HP.Conics.redC p A` reduces a coefficient vector mod `p^2` to one mod `p`;
`Work.HP.Conics.SharpAt ā v` is sharpness of the reduction on the line `⟨v⟩`;
`Work.HP.Conics.II p A v = ∃ v', IsLift p v' v ∧ qf A v' ≠ 0`.  For a sharp `ā` on the line
`⟨v⟩`, exactly `(p-1)p^5` of the `p^6` lifts `A` satisfy `II p A v`.

Suggested route.  Fix a lift `ṽ` of `v` (exists since reduction is surjective).
1. `qf A (ṽ + p w) = qf A ṽ + p · pol A ṽ w` (`Work.HP.Conics.qf_add_smul` with `c = p`,
   `qf A (p w) = p^2 qf A w = 0`), and `red (pol A ṽ w) = pol ā v (red w) = 0` by the radical
   hypothesis (`Work.HP.Conics.red_pol`); hence `qf A (ṽ + p w) = qf A ṽ`, i.e. `qf` is constant
   on the lifts of `v`.  So `II p A v ↔ qf A ṽ ≠ 0`.  (This also gives the helper
   `lift_indep`: `pol (redC p A) v · ≡ 0` implies `qf A v₁ = qf A v₂` for two lifts `v₁,v₂`.)
2. `SharpAt` gives `v ∈ rad`, hence `pol ā v v = 0`; with `qf_smul`, `pol ā v v = 2 * qf ā v`,
   so `qf ā v = 0` since `p ≠ 2`.
3. Parametrise the lifts: each coefficient of `A` is a lift of the corresponding coefficient of
   `ā`, and `A = ã + p·B̃` where `ã` is a fixed lift and `B̃` lifts `B : Mon 2 2 → ZMod p`
   (the map `(ZMod p)^6 →` lifts is a bijection).  By linearity of `qf` in the coefficients,
   `qf A ṽ = qf ã ṽ + p · qf B̃ ṽ`, and `qf B̃ ṽ ≡ qf B (red ṽ) (mod p)`; since `red ṽ = v ≠ 0`,
   `B ↦ qf B v` is a surjective linear functional `(ZMod p)^6 → ZMod p` (a coordinate `v i ≠ 0`
   gives `qf B v = 1` for the coefficient vector of `x_i²` scaled), so it takes each value
   exactly `p^5` times.  And `qf ã ṽ ≡ qf ā v = 0 (mod p)`, so `qf A ṽ` takes each value of
   `p · ZMod p` exactly `p^5` times: it vanishes on `p^5` lifts and is nonzero on `(p-1)p^5`. -/
theorem conics_lift (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (ā : Mon 2 2 → ZMod p)
    (v : Fin 3 → ZMod p) (hv : Work.HP.Conics.SharpAt ā v) :
    {A : Mon 2 2 → ZMod (p^2) | Work.HP.Conics.redC p A = ā ∧ Work.HP.Conics.II p A v}.ncard
      = (p - 1) * p ^ 5 := by
  have qfPhi : ∀ B : Mon 2 2 → ZMod p, qf (Phi p ā B) (vecLift p v)
      = qf (coefLift p ā) (vecLift p v) + (p : ZMod (p ^ 2)) * lif p (qf B v) :=
    fun B => conics_lift_qfPhi p ā v B
  have hv0 : v ≠ 0 := hv.1
  have hrad : ∀ y : Fin 3 → ZMod p, pol ā v y = 0 := hv.2.1
  have indep : ∀ (A : Mon 2 2 → ZMod (p ^ 2)) (v₁ v₂ : Fin 3 → ZMod (p ^ 2)),
      redC p A = ā → IsLift p v₁ v → IsLift p v₂ v → qf A v₁ = qf A v₂ :=
    fun A v₁ v₂ hA h₁ h₂ => conics_lift_indep p ā v hrad A hA v₁ v₂ h₁ h₂
  have fiber : ∀ c : ZMod p, Fintype.card {B : Mon 2 2 → ZMod p // qf B v = c} = p ^ 5 :=
    fun c => conics_lift_fiber p v hv0 c
  have hqfv : qf ā v = 0 := qf_sharp_zero p hp ā v hv
  have hredqf : red p (qf (coefLift p ā) (vecLift p v)) = 0 := by
    rw [red_qf]
    have h1 : redC p (coefLift p ā) = ā := by funext m; exact red_lif p (ā m)
    have h2 : (fun i => red p (vecLift p v i)) = v := by funext i; exact red_lif p (v i)
    rw [h1, h2]
    exact hqfv
  obtain ⟨c₀, hc₀⟩ := (red_eq_zero_iff_exists_lif p _).mp hredqf
  have hkey : ∀ B : Mon 2 2 → ZMod p,
      qf (Phi p ā B) (vecLift p v) = (p : ZMod (p ^ 2)) * lif p (c₀ + qf B v) := by
    intro B
    rw [qfPhi B, hc₀, ← mul_add]
    conv_lhs => rw [p_mul_eq_p_mul_lif_red]
    rw [map_add, red_lif, red_lif]
  have hkey_ne : ∀ B : Mon 2 2 → ZMod p,
      (qf (Phi p ā B) (vecLift p v) ≠ 0) ↔ (c₀ + qf B v ≠ 0) := by
    intro B
    rw [hkey B]
    exact (p_mul_lif_eq_zero_iff p (c₀ + qf B v)).not
  have hliftvec : IsLift p (vecLift p v) v := fun i => red_lif p (v i)
  have hII : ∀ A : Mon 2 2 → ZMod (p ^ 2), redC p A = ā →
      (II p A v ↔ qf A (vecLift p v) ≠ 0) := by
    intro A hA
    constructor
    · rintro ⟨v', hv', hne⟩
      have h := indep A v' (vecLift p v) hA hv' hliftvec
      rwa [h] at hne
    · rintro h
      exact ⟨vecLift p v, hliftvec, h⟩
  have hset : {A : Mon 2 2 → ZMod (p ^ 2) | redC p A = ā ∧ II p A v}
      = Phi p ā '' {B : Mon 2 2 → ZMod p | c₀ + qf B v ≠ 0} := by
    ext A
    constructor
    · rintro ⟨hA, hIIA⟩
      obtain ⟨B, hB⟩ := Phi_surjective p ā A hA
      refine ⟨B, ?_, hB⟩
      have hthis : qf A (vecLift p v) ≠ 0 := (hII A hA).mp hIIA
      rw [← hB] at hthis
      exact (hkey_ne B).mp hthis
    · rintro ⟨B, hB, rfl⟩
      exact ⟨redC_Phi p ā B,
        (hII (Phi p ā B) (redC_Phi p ā B)).mpr ((hkey_ne B).mpr hB)⟩
  have hcardT : Fintype.card {B : Mon 2 2 → ZMod p // c₀ + qf B v ≠ 0} = (p - 1) * p ^ 5 := by
    have hiff : ∀ B : Mon 2 2 → ZMod p, c₀ + qf B v = 0 ↔ qf B v = -c₀ := by
      intro B; rw [add_comm, add_eq_zero_iff_eq_neg]
    have hzero : Fintype.card {B : Mon 2 2 → ZMod p // c₀ + qf B v = 0} = p ^ 5 := by
      rw [Fintype.card_congr (Equiv.subtypeEquivRight hiff)]
      exact fiber (-c₀)
    have htotal : Fintype.card (Mon 2 2 → ZMod p) = p ^ 6 := by
      rw [Fintype.card_fun, ZMod.card, card_mon]
    rw [Fintype.card_subtype_compl (fun B : Mon 2 2 → ZMod p => c₀ + qf B v = 0),
      hzero, htotal, Nat.sub_mul, one_mul, ← pow_succ']
  have hTal : {B : Mon 2 2 → ZMod p | c₀ + qf B v ≠ 0}.ncard = (p - 1) * p ^ 5 := by
    rw [← Set.fintypeCard_eq_ncard]
    exact hcardT
  rw [hset, Set.ncard_image_of_injective _ (Phi_injective p ā), hTal]

end Work.HP
