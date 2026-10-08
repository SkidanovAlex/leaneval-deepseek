import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.higman_lemma2
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.higman_lemma3_base
import Submission.Work.Higman.higman_lemma3_delta
import Submission.Work.Higman.xi_trans_quot_sq
import Submission.Work.Higman.higman_lemma10
import Submission.Work.Higman.boolean_idempotent_family_mul
import Submission.Work.Higman.higman_lemma3_final_step

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped commutatorElement

namespace Work.Higman

/-- **Higman 1963, Lemma 3.**  Let `A` be a normal abelian `ξ`-subgroup of a Suzuki 2-group `P`
and `C` a normal `ξ`-subgroup covering `A` (`C/A` a minimal normal `ξ`-section).  If
`Φ(C) = Φ(A) = A²`, then `A` has exponent at most `4`. -/
theorem higman_lemma3_aux {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hPhi : Work.Higman.powSub C 2 ⊔ ⁅C, C⁆ = Work.Higman.powSub A 2) :
    ∀ a ∈ A, a ^ 4 = 1 := by
  rcases eq_or_ne A ⊥ with hbot | hne
  · intro a ha
    rw [hbot] at ha
    simp only [Subgroup.mem_bot] at ha
    subst ha
    simp
  have hAis : IsXiAbelNormal h A := hA
  obtain ⟨hAn, hAinv, hAb⟩ := hAis
  obtain ⟨D⟩ := exists_homocyclicData h ⟨hAn, hAinv, hAb⟩
  have hC2 : powSub C 2 ≤ powSub A 2 := by rw [← hPhi]; exact le_sup_left
  have hCC : ⁅C, C⁆ ≤ powSub A 2 := by rw [← hPhi]; exact le_sup_right
  -- `A ⊓ Ω₁ ≠ ⊥`
  have hneA : A ⊓ omega1 P ≠ ⊥ := by
    have hcard : 2 ∣ Nat.card ↥A := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (h.isPGroup.to_subgroup A)
      have hnt : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hne
      have h2 : 2 ≤ Nat.card ↥A := by
        have := Finite.one_lt_card_iff_nontrivial.mpr hnt
        omega
      rw [hn] at h2 ⊢
      rcases Nat.eq_zero_or_pos n with hn0 | hpos
      · rw [hn0] at h2; norm_num at h2
      · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
        rw [hm]
        exact ⟨2 ^ m, by rw [pow_succ, mul_comm]⟩
    obtain ⟨x, hx2⟩ := exists_prime_orderOf_dvd_card' 2 hcard
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨(x : P), ⟨x.2, ?_⟩⟩, ?_⟩
    · change (x : P) ∈ omega1 P
      rw [h.mem_omega1, ← orderOf_dvd_iff_pow_eq_one, Subgroup.orderOf_coe, hx2]
    · intro hc
      have hxe : (x : P) = 1 := Subtype.ext_iff.mp hc
      have h1 : orderOf (x : P) = 1 := by rw [hxe, orderOf_one]
      have h21 : (2:ℕ) = 1 := ((Subgroup.orderOf_coe x).trans hx2).symm.trans h1
      exact absurd h21 (by norm_num)
  have hOn : omega1 P ≤ A := by
    have hSin : (A ⊓ omega1 P).map (h.xi : MulAut P).toMonoidHom = A ⊓ omega1 P := by
      rw [← D.hT, map_powSub (h.xi : MulAut P) hAinv]
    have hSle : A ⊓ omega1 P ≤ (⊤ : Subgroup P) ⊓ omega1 P := by simp
    rcases inf_omega1_eq_bot_or_top h hSle hSin with hb | htop
    · exact absurd hb hneA
    · have htop' : A ⊓ omega1 P = omega1 P := by rw [htop]; simp
      rw [← htop']
      exact inf_le_left
  suffices hgoal : powSub A 4 = ⊥ by
    intro a ha
    have : a ^ 4 ∈ (⊥ : Subgroup P) := by rw [← hgoal]; exact pow_mem_powSub ha
    simpa using Subgroup.mem_bot.mp this
  by_contra h4ne
  have h3 : 3 ≤ D.e := by
    by_contra hcon
    have he : D.e ≤ 2 := by omega
    have hmul : 2 ^ D.e * 2 ^ (2 - D.e) = 4 := by
      rw [← pow_add, Nat.add_sub_cancel' he]
      norm_num
    exact h4ne (by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      obtain ⟨a, ha, rfl⟩ := (mem_powSub_iff hAb).mp hz
      rw [show a ^ 4 = (a ^ 2 ^ D.e) ^ 2 ^ (2 - D.e) from by rw [← pow_mul, hmul],
        D.hexp a ha, one_pow])
  have hcard0 : Nat.card ↥A = qcard A ^ D.e := by
    rw [show Nat.card ↥A = Nat.card ↥(powSub A (2 ^ 0)) from by rw [pow_zero, powSub_one_eq]]
    exact D.hcard 0 (Nat.zero_le _)
  have hq2 : 2 ≤ qcard A := by
    have h2 : 2 ≤ Nat.card ↥A := by
      have hnt : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hne
      have := Finite.one_lt_card_iff_nontrivial.mpr hnt
      omega
    by_contra hc
    have hc1 : qcard A ≤ 1 := by omega
    have hle : qcard A ^ D.e ≤ 1 := by
      calc qcard A ^ D.e ≤ 1 ^ D.e := Nat.pow_le_pow_left hc1 D.e
        _ = 1 := one_pow _
    omega
  have hq4 : 4 ≤ qcard A := by
    have h1 : qcard A = Nat.card ↥(omega1 P) := by
      rw [qcard, show A ⊓ omega1 P = omega1 P from inf_of_le_right hOn]
    rw [h1]
    exact h.omega1_card_ge_four
  -- ### The quotient `W = A / A²`
  have hcommA : ∀ a b : ↥A, a * b = b * a := fun a b => Subtype.ext (hAb a a.2 b b.2)
  have memK_iff : ∀ {z : ↥A}, z ∈ (powSub A 2).subgroupOf A ↔ (z : P) ∈ powSub A 2 :=
    fun {z} => Subgroup.mem_subgroupOf
  have hKnormal : ((powSub A 2).subgroupOf A).Normal := by
    refine Subgroup.Normal.mk (fun n hn g => ?_)
    rw [memK_iff] at hn ⊢
    have hval : ((g * n * g⁻¹ : ↥A) : P) = (n : P) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact conj_eq_of_abelian hAb g.2 n.2
    rw [hval]; exact hn
  haveI hKn : ((powSub A 2).subgroupOf A).Normal := hKnormal
  let W : Type := ↥A ⧸ (powSub A 2).subgroupOf A
  have hW2 : ∀ g : W, g * g = 1 := by
    intro g
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (N := (powSub A 2).subgroupOf A) g
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have h2 : (a : P) ^ 2 ∈ powSub A 2 := pow_mem_powSub (A := A) (n := 2) a.2
    simpa [Subgroup.coe_mul, pow_two] using h2
  have sq_eq_one_memK : ∀ {z : ↥A}, z * z = 1 → z ∈ (powSub A 2).subgroupOf A := by
    intro z hz
    rw [memK_iff]
    refine mem_powSub_two_of_sq_eq_one h hA D h3 z.2 ?_
    have hh := congrArg (fun t : ↥A => (t : P)) hz
    simpa [Subgroup.coe_mul, pow_two] using hh
  have exists_root : ∀ y : ↥((powSub A 2).subgroupOf A), ∃ x : ↥A, x * x = y.1 := by
    intro y
    obtain ⟨c, hc, hc2⟩ := (mem_powSub_iff hAb).mp ((memK_iff).mp y.2)
    exact ⟨⟨c, hc⟩, Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two]; exact hc2)⟩
  let rhoF : ↥((powSub A 2).subgroupOf A) → ↥A := fun y => Classical.choose (exists_root y)
  have rhoF_spec : ∀ y : ↥((powSub A 2).subgroupOf A), rhoF y * rhoF y = y.1 :=
    fun y => Classical.choose_spec (exists_root y)
  have mk_eq_of_sq_eq : ∀ {u v : ↥A}, u * u = v * v →
      (QuotientGroup.mk u : W) = QuotientGroup.mk v := by
    intro u v huv
    change (QuotientGroup.mk' ((powSub A 2).subgroupOf A)) u
      = (QuotientGroup.mk' ((powSub A 2).subgroupOf A)) v
    rw [QuotientGroup.mk'_eq_mk']
    refine ⟨u⁻¹ * v, ?_, by group⟩
    apply sq_eq_one_memK
    have hcommv : v * u⁻¹ = u⁻¹ * v := Subtype.ext (hAb v v.2 u⁻¹ (A.inv_mem u.2))
    calc (u⁻¹ * v) * (u⁻¹ * v) = u⁻¹ * ((v * u⁻¹) * v) := by group
      _ = u⁻¹ * ((u⁻¹ * v) * v) := by rw [hcommv]
      _ = (u⁻¹ * u⁻¹) * (v * v) := by group
      _ = (u * u)⁻¹ * (v * v) :=
            congrArg (fun t : ↥A => t * (v * v)) (mul_inv_rev u u).symm
      _ = (u * u)⁻¹ * (u * u) := by rw [huv]
      _ = 1 := inv_mul_cancel _
  have mk_eq_of_sq_eq_one : ∀ {u v : ↥A}, (u * v⁻¹) * (u * v⁻¹) = 1 →
      (QuotientGroup.mk u : W) = QuotientGroup.mk v := by
    intro u v huv
    have hmem : u * v⁻¹ ∈ (powSub A 2).subgroupOf A := sq_eq_one_memK huv
    have hmem' : u⁻¹ * v ∈ (powSub A 2).subgroupOf A := by
      have h1 : u⁻¹ * v = (u * v⁻¹)⁻¹ := by
        apply Subtype.ext
        show ((u : P))⁻¹ * (v : P) = ((u : P) * (v : P)⁻¹)⁻¹
        rw [mul_inv_rev, inv_inv]
        exact hAb u⁻¹ (A.inv_mem u.2) v v.2
      rw [h1]
      exact Subgroup.inv_mem _ hmem
    change (QuotientGroup.mk' ((powSub A 2).subgroupOf A)) u
      = (QuotientGroup.mk' ((powSub A 2).subgroupOf A)) v
    rw [QuotientGroup.mk'_eq_mk']
    exact ⟨u⁻¹ * v, hmem', by group⟩
  let rho : ↥((powSub A 2).subgroupOf A) →* W :=
    { toFun := fun y => QuotientGroup.mk (rhoF y)
      map_one' := by
        refine (QuotientGroup.eq_one_iff (rhoF 1)).mpr ?_
        apply sq_eq_one_memK
        have h := rhoF_spec 1
        simpa using h
      map_mul' := fun y y' => by
        apply mk_eq_of_sq_eq
        have hc : rhoF y' * rhoF y = rhoF y * rhoF y' := hcommA _ _
        calc rhoF (y * y') * rhoF (y * y') = (y * y').1 := rhoF_spec (y * y')
          _ = y.1 * y'.1 := rfl
          _ = (rhoF y * rhoF y) * (rhoF y' * rhoF y') := by rw [rhoF_spec y, rhoF_spec y']
          _ = rhoF y * ((rhoF y * rhoF y') * rhoF y') := by group
          _ = rhoF y * ((rhoF y' * rhoF y) * rhoF y') := by rw [hc]
          _ = (rhoF y * rhoF y') * (rhoF y * rhoF y') := by group }
  have rho_eq_one_iff : ∀ y : ↥((powSub A 2).subgroupOf A),
      rho y = 1 ↔ ((y.1 : ↥A) : P) ∈ powSub A 4 := by
    intro y
    constructor
    · intro h1
      have h2 : rhoF y ∈ (powSub A 2).subgroupOf A :=
        (QuotientGroup.eq_one_iff (rhoF y)).mp h1
      have h3 : ((rhoF y : ↥A) : P) ∈ powSub A 2 := (memK_iff).mp h2
      have h4 : ((y.1 : ↥A) : P) = ((rhoF y : ↥A) : P) * ((rhoF y : ↥A) : P) := by
        have hh := congrArg (fun t : ↥A => (t : P)) (rhoF_spec y)
        simpa [Subgroup.coe_mul] using hh.symm
      rw [h4]
      have h5 : ((rhoF y : ↥A) : P) ^ 2 ∈ powSub A 4 := by
        have h6 : ((rhoF y : ↥A) : P) ^ 2 ∈ powSub (powSub A 2) 2 :=
          pow_mem_powSub (A := powSub A 2) (n := 2) h3
        rwa [powSub_powSub hAb 2 2] at h6
      simpa [pow_two] using h5
    · intro hy
      have hy' : ((y.1 : ↥A) : P) ∈ powSub (powSub A 2) 2 := by
        rwa [powSub_powSub hAb 2 2]
      obtain ⟨c, hc, hc2⟩ := (mem_powSub_iff (powSub_comm hAb 2)).mp hy'
      have hcA : c ∈ A := powSub_le (by norm_num : 0 < (2:ℕ)) hc
      have hcK : (⟨c, hcA⟩ : ↥A) ∈ (powSub A 2).subgroupOf A := (memK_iff).mpr hc
      have heq : (⟨c, hcA⟩ : ↥A) * ⟨c, hcA⟩ = y.1 := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, ← pow_two]
        exact hc2
      have hmk : (QuotientGroup.mk (rhoF y) : W) = QuotientGroup.mk (⟨c, hcA⟩ : ↥A) :=
        mk_eq_of_sq_eq (by rw [rhoF_spec y, heq])
      show (QuotientGroup.mk (rhoF y) : W) = 1
      rw [hmk, QuotientGroup.eq_one_iff]
      exact hcK
  -- ### `δ` composed with inversion, as a map into `A²`
  let deltaToK : ∀ u : ↥C, ↥A →* ↥((powSub A 2).subgroupOf A) := fun u =>
    { toFun := fun a => ⟨(deltaA hAn u a)⁻¹,
        (memK_iff).mpr (Subgroup.inv_mem _ (deltaA_mem_powSub_two h hA hAn hAb u a))⟩
      map_one' := by
        apply Subtype.ext
        show ((deltaA hAn u 1)⁻¹ : ↥A) = (1 : ↥A)
        rw [deltaA_one hAn u]
        exact inv_one
      map_mul' := fun a b => by
        apply Subtype.ext
        show ((deltaA hAn u (a * b))⁻¹ : ↥A) = (deltaA hAn u a)⁻¹ * (deltaA hAn u b)⁻¹
        rw [deltaA_mul hAn hAb u a b]
        exact (mul_inv_rev (deltaA hAn u a) (deltaA hAn u b)).trans
          (hcommA (deltaA hAn u a)⁻¹ (deltaA hAn u b)⁻¹).symm }
  have coe_deltaToK : ∀ (u : ↥C) (a : ↥A),
      (((deltaToK u) a : ↥((powSub A 2).subgroupOf A)) : P)
        = (((deltaA hAn u a : ↥A) : P))⁻¹ := by
    intro u a
    simp only [deltaToK]
    rfl
  have KK_ker : ∀ u : ↥C, (powSub A 2).subgroupOf A ≤ (rho.comp (deltaToK u)).ker := by
    intro u x hx
    rw [MonoidHom.mem_ker]
    show rho ((deltaToK u) x) = 1
    rw [rho_eq_one_iff, coe_deltaToK]
    exact inv_mem_iff.mpr
      (deltaA_mem_powSub_four_of_mem_powSub_two h hA hAn hAb u x.2 ((memK_iff).mp hx))
  let nuBarF : ↥C → W →* W := fun u =>
    QuotientGroup.lift (N := (powSub A 2).subgroupOf A) (rho.comp (deltaToK u)) (KK_ker u)
  have nuBar_mk : ∀ (u : ↥C) (a : ↥A),
      nuBarF u (QuotientGroup.mk a) = rho (deltaToK u a) :=
    fun u a => QuotientGroup.lift_mk'
      (N := (powSub A 2).subgroupOf A) (φ := rho.comp (deltaToK u)) (KK_ker u) a
  have nuBar_zero_iff : ∀ (u : ↥C) (a : ↥A),
      nuBarF u (QuotientGroup.mk a) = 1 ↔ ((deltaA hAn u a : ↥A) : P) ∈ powSub A 4 := by
    intro u a
    rw [nuBar_mk, rho_eq_one_iff, coe_deltaToK]
    constructor
    · intro hh; rwa [inv_mem_iff] at hh
    · intro hh; rwa [inv_mem_iff]
  have deltaToK_val : ∀ (u : ↥C) (a : ↥A),
      (((deltaToK u) a : ↥((powSub A 2).subgroupOf A)) : ↥A) = (deltaA hAn u a)⁻¹ :=
    fun u a => rfl
  have mk_eq_of_memK : ∀ {u v : ↥A}, u * v⁻¹ ∈ (powSub A 2).subgroupOf A →
      (QuotientGroup.mk u : W) = QuotientGroup.mk v := by
    intro u v huv
    change (QuotientGroup.mk' ((powSub A 2).subgroupOf A)) u
      = (QuotientGroup.mk' ((powSub A 2).subgroupOf A)) v
    rw [QuotientGroup.mk'_eq_mk']
    refine ⟨u⁻¹ * v, ?_, by group⟩
    have h1 : (u * v⁻¹)⁻¹ ∈ (powSub A 2).subgroupOf A := Subgroup.inv_mem _ huv
    rw [show (u * v⁻¹)⁻¹ = u⁻¹ * v from by
      rw [mul_inv_rev, inv_inv]
      exact hcommA v u⁻¹] at h1
    exact h1
  have hδinv : ∀ (u : ↥C) (b : ↥A), deltaA hAn u b⁻¹ = (deltaA hAn u b)⁻¹ := by
    intro u b
    have h1 : deltaA hAn u b * deltaA hAn u b⁻¹
        = deltaA hAn u b * (deltaA hAn u b)⁻¹ := by
      rw [← deltaA_mul hAn hAb u b b⁻¹, mul_inv_cancel, deltaA_one hAn u, mul_inv_cancel]
    exact mul_left_cancel h1
  -- ### idempotence of `ν̄(u)`
  have nuBar_idem : ∀ (u : ↥C) (g : W), nuBarF u (nuBarF u g) = nuBarF u g := by
    intro u g
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (N := (powSub A 2).subgroupOf A) g
    show nuBarF u (rho ((deltaToK u) a)) = rho ((deltaToK u) a)
    change nuBarF u (QuotientGroup.mk (rhoF ((deltaToK u) a)))
      = QuotientGroup.mk (rhoF ((deltaToK u) a))
    rw [nuBar_mk]
    change (QuotientGroup.mk (rhoF ((deltaToK u) (rhoF ((deltaToK u) a)))) : W)
      = QuotientGroup.mk (rhoF ((deltaToK u) a))
    set x : ↥A := rhoF ((deltaToK u) a) with hxdef
    have hx2 : x * x = (deltaA hAn u a)⁻¹ := by
      rw [hxdef, rhoF_spec]
      exact deltaToK_val u a
    set y : ↥A := rhoF ((deltaToK u) x) with hydef
    have hy2 : y * y = (deltaA hAn u x)⁻¹ := by
      rw [hydef, rhoF_spec]
      exact deltaToK_val u x
    have hδ : deltaA hAn u x * deltaA hAn u x = deltaA hAn u a * deltaA hAn u a := by
      have h2 : deltaA hAn u (x * x) = deltaA hAn u x * deltaA hAn u x :=
        deltaA_mul hAn hAb u x x
      rw [← h2, hx2, hδinv u (deltaA hAn u a), deltaA_deltaA hAn hAb hC2 u a]
      have hfin : ((deltaA hAn u a)⁻¹ * (deltaA hAn u a)⁻¹)⁻¹
          = deltaA hAn u a * deltaA hAn u a := by
        rw [show ((deltaA hAn u a)⁻¹ * (deltaA hAn u a)⁻¹)⁻¹
            = (((deltaA hAn u a) * (deltaA hAn u a))⁻¹)⁻¹ from
              congrArg Inv.inv (mul_inv_rev (deltaA hAn u a) (deltaA hAn u a)).symm]
        exact inv_inv _
      exact hfin
    have h4 : (y * x⁻¹) ^ 4 = 1 := by
      have hsq : (y * x⁻¹) * (y * x⁻¹) = (deltaA hAn u x)⁻¹ * (deltaA hAn u a) := by
        have hc : x⁻¹ * y = y * x⁻¹ := hcommA x⁻¹ y
        calc (y * x⁻¹) * (y * x⁻¹) = y * ((x⁻¹ * y) * x⁻¹) := by group
          _ = y * ((y * x⁻¹) * x⁻¹) := by rw [hc]
          _ = (y * y) * (x⁻¹ * x⁻¹) := by group
          _ = (y * y) * (x * x)⁻¹ :=
                congrArg (fun t => (y * y) * t) (mul_inv_rev x x).symm
          _ = (deltaA hAn u x)⁻¹ * (deltaA hAn u a) := by rw [hy2, hx2, inv_inv]
      have hc2 : (deltaA hAn u x)⁻¹ * (deltaA hAn u a)
          = (deltaA hAn u a) * (deltaA hAn u x)⁻¹ := hcommA _ _
      rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, pow_two, pow_two, hsq, hc2]
      have h3 : (deltaA hAn u a) * (deltaA hAn u x)⁻¹
            * ((deltaA hAn u a) * (deltaA hAn u x)⁻¹)
          = ((deltaA hAn u x) * (deltaA hAn u x))⁻¹
            * ((deltaA hAn u a) * (deltaA hAn u a)) := by
        have hc3 : (deltaA hAn u x)⁻¹ * (deltaA hAn u a)
            = (deltaA hAn u a) * (deltaA hAn u x)⁻¹ := hcommA _ _
        calc (deltaA hAn u a) * (deltaA hAn u x)⁻¹
              * ((deltaA hAn u a) * (deltaA hAn u x)⁻¹)
            = (deltaA hAn u a)
              * (((deltaA hAn u x)⁻¹ * (deltaA hAn u a)) * (deltaA hAn u x)⁻¹) := by group
          _ = (deltaA hAn u a)
              * (((deltaA hAn u a) * (deltaA hAn u x)⁻¹) * (deltaA hAn u x)⁻¹) := by rw [hc3]
          _ = ((deltaA hAn u a) * (deltaA hAn u a))
              * ((deltaA hAn u x)⁻¹ * (deltaA hAn u x)⁻¹) := by group
          _ = ((deltaA hAn u a) * (deltaA hAn u a))
              * ((deltaA hAn u x) * (deltaA hAn u x))⁻¹ :=
                congrArg (fun t => ((deltaA hAn u a) * (deltaA hAn u a)) * t)
                  (mul_inv_rev (deltaA hAn u x) (deltaA hAn u x)).symm
          _ = ((deltaA hAn u x) * (deltaA hAn u x))⁻¹
              * ((deltaA hAn u a) * (deltaA hAn u a)) := hcommA _ _
      rw [h3]
      rw [hδ, inv_mul_cancel]
    apply mk_eq_of_memK
    rw [memK_iff, Subgroup.coe_mul, Subgroup.coe_inv]
    have h4p := congrArg (fun t : ↥A => (t : P)) h4
    have h4q : ((y : P) * (x : P)⁻¹) ^ 4 = 1 := by
      simpa [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] using h4p
    exact mem_powSub_two_of_pow_four_eq_one h hA D h3 (A.mul_mem y.2 (A.inv_mem x.2)) h4q
  -- ### multiplicativity in `u`
  have nuBar_mul : ∀ (u v : ↥C) (g : W), nuBarF (u*v) g = nuBarF u g * nuBarF v g := by
    intro u v g
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (N := (powSub A 2).subgroupOf A) g
    change nuBarF (u*v) (QuotientGroup.mk a)
      = nuBarF u (QuotientGroup.mk a) * nuBarF v (QuotientGroup.mk a)
    rw [nuBar_mk, nuBar_mk, nuBar_mk]
    change (QuotientGroup.mk (rhoF ((deltaToK (u*v)) a)) : W)
      = QuotientGroup.mk (rhoF ((deltaToK u) a) * rhoF ((deltaToK v) a))
    set p : ↥A := rhoF ((deltaToK u) a) with hpdef
    set q : ↥A := rhoF ((deltaToK v) a) with hqdef
    set z : ↥A := rhoF ((deltaToK (u*v)) a) with hzdef
    have hp2 : p * p = (deltaA hAn u a)⁻¹ := by
      rw [hpdef, rhoF_spec]; exact deltaToK_val u a
    have hq2 : q * q = (deltaA hAn v a)⁻¹ := by
      rw [hqdef, rhoF_spec]; exact deltaToK_val v a
    have hz2 : z * z = (deltaA hAn (u*v) a)⁻¹ := by
      rw [hzdef, rhoF_spec]; exact deltaToK_val (u*v) a
    have hduv : deltaA hAn (u*v) a
        = deltaA hAn u a * deltaA hAn v a * deltaA hAn v (deltaA hAn u a) :=
      deltaA_mul_uv hAn hAb u v a
    have hpq2 : (p * q) * (p * q) = (deltaA hAn u a)⁻¹ * (deltaA hAn v a)⁻¹ := by
      have hc : q * p = p * q := hcommA q p
      calc (p * q) * (p * q) = p * ((q * p) * q) := by group
        _ = p * ((p * q) * q) := by rw [hc]
        _ = (p * p) * (q * q) := by group
        _ = (deltaA hAn u a)⁻¹ * (deltaA hAn v a)⁻¹ := by rw [hp2, hq2]
    have hδv4 : (((deltaA hAn v (deltaA hAn u a) : ↥A)) : P) ∈ powSub A 4 :=
      deltaA_mem_powSub_four_of_mem_powSub_two h hA hAn hAb v (deltaA hAn u a).2
        (deltaA_mem_powSub_two h hA hAn hAb u a)
    have hzq : (z * (p * q)⁻¹) * (z * (p * q)⁻¹)
        = (deltaA hAn v (deltaA hAn u a))⁻¹ := by
      have hc : (p * q)⁻¹ * z = z * (p * q)⁻¹ := hcommA _ _
      calc (z * (p * q)⁻¹) * (z * (p * q)⁻¹)
          = z * (((p*q)⁻¹ * z) * (p*q)⁻¹) := by group
        _ = z * ((z * (p*q)⁻¹) * (p*q)⁻¹) := by rw [hc]
        _ = (z * z) * ((p*q)⁻¹ * (p*q)⁻¹) := by group
        _ = (z * z) * ((p*q) * (p*q))⁻¹ :=
              congrArg (fun t => (z * z) * t) (mul_inv_rev (p*q) (p*q)).symm
        _ = (deltaA hAn (u*v) a)⁻¹ * ((deltaA hAn u a)⁻¹ * (deltaA hAn v a)⁻¹)⁻¹ := by
              rw [hz2, hpq2]
        _ = (deltaA hAn v (deltaA hAn u a))⁻¹ := by
              rw [hduv]
              have h1 : ((deltaA hAn u a)⁻¹ * (deltaA hAn v a)⁻¹)⁻¹
                  = deltaA hAn u a * deltaA hAn v a := by
                have hcomm : (deltaA hAn u a)⁻¹ * (deltaA hAn v a)⁻¹
                    = (deltaA hAn v a)⁻¹ * (deltaA hAn u a)⁻¹ := hcommA _ _
                rw [hcomm]
                calc ((deltaA hAn v a)⁻¹ * (deltaA hAn u a)⁻¹)⁻¹
                    = (((deltaA hAn u a) * (deltaA hAn v a))⁻¹)⁻¹ :=
                      (congrArg Inv.inv (mul_inv_rev (deltaA hAn u a) (deltaA hAn v a))).symm
                  _ = deltaA hAn u a * deltaA hAn v a := inv_inv _
              rw [h1]
              calc (deltaA hAn u a * deltaA hAn v a * deltaA hAn v (deltaA hAn u a))⁻¹
                    * (deltaA hAn u a * deltaA hAn v a)
                  = ((deltaA hAn v (deltaA hAn u a))⁻¹
                      * (deltaA hAn u a * deltaA hAn v a)⁻¹)
                    * (deltaA hAn u a * deltaA hAn v a) := by
                    rw [mul_inv_rev]
                _ = (deltaA hAn v (deltaA hAn u a))⁻¹ := by
                    rw [mul_assoc, inv_mul_cancel, mul_one]
    apply mk_eq_of_memK
    rw [memK_iff]
    apply mem_powSub_two_of_sq_mem_powSub_four h hA D h3
      (A.mul_mem z.2 (A.inv_mem (A.mul_mem p.2 q.2)))
    have h1 := congrArg (fun t : ↥A => (t : P)) hzq
    rw [pow_two]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1 ⊢
    rw [h1]
    exact Subgroup.inv_mem _ hδv4
  -- ### the `ξ`-action on `W` and the Boolean idempotent family
  let xiAut : ↥A ≃* ↥A :=
    { toFun := xiA h hAinv
      invFun := xiAinv h hAinv
      left_inv := fun a => by
        apply Subtype.ext
        show (h.xi : MulAut P).symm (h.xi (a : P)) = (a : P)
        exact MulEquiv.symm_apply_apply (h.xi : MulAut P) (a : P)
      right_inv := fun a => by
        apply Subtype.ext
        show h.xi ((h.xi : MulAut P).symm (a : P)) = (a : P)
        exact MulEquiv.apply_symm_apply (h.xi : MulAut P) (a : P)
      map_mul' := fun a b => by
        apply Subtype.ext
        show h.xi ((a : P) * (b : P)) = h.xi (a : P) * h.xi (b : P)
        exact map_mul (h.xi : MulAut P) (a : P) (b : P) }
  have xiAut_coe : ∀ a : ↥A, (((xiAut a : ↥A)) : P) = h.xi (a : P) := by
    intro a
    rfl
  have hKxi : ((powSub A 2).subgroupOf A).map xiAut = (powSub A 2).subgroupOf A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change ((xiAut y : ↥A) : P) ∈ powSub A 2
      have hy' : (y : P) ∈ powSub A 2 := (memK_iff).mp hy
      rw [xiAut_coe]
      have hmem : h.xi (y : P) ∈ (powSub A 2).map (h.xi : MulAut P).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hy'
      rwa [map_powSub (h.xi : MulAut P) hAinv 2] at hmem
    · intro hx
      refine ⟨xiAinv h hAinv x, ?_, ?_⟩
      · change (((xiAinv h hAinv x : ↥A)) : P) ∈ powSub A 2
        exact symm_mem_of_map_eq (h.xi : MulAut P) (map_powSub (h.xi : MulAut P) hAinv 2)
          ((memK_iff).mp hx)
      · apply Subtype.ext
        show h.xi ((h.xi : MulAut P).symm (x : P)) = (x : P)
        exact MulEquiv.apply_symm_apply (h.xi : MulAut P) (x : P)
  let xiW : W ≃* W :=
    QuotientGroup.congr ((powSub A 2).subgroupOf A) ((powSub A 2).subgroupOf A) xiAut hKxi
  have xiW_mk : ∀ a : ↥A, xiW (QuotientGroup.mk a : W) = QuotientGroup.mk (xiAut a) := by
    intro a
    show (QuotientGroup.congr _ _ xiAut hKxi) (QuotientGroup.mk a) = _
    rw [QuotientGroup.congr_mk]
  have xiAut_pow_coe : ∀ (k : ℕ) (c : ↥A),
      (((xiAut ^ k) c : ↥A) : P) = (h.xi ^ k) (c : P) := by
    intro k
    induction k with
    | zero => intro c; simp
    | succ k ih =>
        intro c
        have h1 : (xiAut ^ (k + 1)) c = (xiAut ^ k) (xiAut c) := by
          rw [pow_succ]; rfl
        rw [h1, ih (xiAut c), xiAut_coe, pow_succ]
        rfl
  have xiW_pow_mk : ∀ (k : ℕ) (a : ↥A),
      (xiW ^ k) (QuotientGroup.mk a : W) = QuotientGroup.mk ((xiAut ^ k) a) := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
        intro a
        have h1 : (xiW ^ (k + 1)) (QuotientGroup.mk a : W)
            = (xiW ^ k) (xiW (QuotientGroup.mk a)) := by
          rw [pow_succ]; rfl
        have h2 : (xiAut ^ (k + 1)) a = (xiAut ^ k) (xiAut a) := by
          rw [pow_succ]; rfl
        rw [h1, xiW_mk, ih (xiAut a), h2]
  have htransW : ∀ g g' : W, g ≠ 1 → g' ≠ 1 → ∃ k : ℕ, (xiW ^ k) g = g' := by
    intro g g' hg hg'
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (N := (powSub A 2).subgroupOf A) g
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (N := (powSub A 2).subgroupOf A) g'
    have haK : (a : P) ∉ powSub A 2 := fun hc =>
      hg ((QuotientGroup.eq_one_iff a).mpr ((memK_iff).mpr hc))
    have hbK : (b : P) ∉ powSub A 2 := fun hc =>
      hg' ((QuotientGroup.eq_one_iff b).mpr ((memK_iff).mpr hc))
    obtain ⟨k, hk⟩ := xi_trans_quot_sq h hA a.2 b.2 haK hbK
    refine ⟨k, ?_⟩
    change (xiW ^ k) (QuotientGroup.mk a : W) = QuotientGroup.mk b
    rw [xiW_pow_mk]
    have h1 : (((xiAut ^ k) a : ↥A) : P) * (b : P)⁻¹ ∈ powSub A 2 := by
      rw [xiAut_pow_coe]
      exact hk
    exact mk_eq_of_memK (by
      rw [memK_iff]
      simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h1)
  -- ### The `ξ`-action on `C` and the equivariance of `ν̄`
  let xiCinv : ↥C → ↥C := fun u =>
    ⟨(h.xi : MulAut P).symm (u : P), symm_mem_of_map_eq h.xi hCinv u.2⟩
  let xiCEq : ↥C ≃* ↥C :=
    { toFun := xiC h hCinv
      invFun := xiCinv
      left_inv := fun u => by
        apply Subtype.ext
        show (h.xi : MulAut P).symm (h.xi (u : P)) = (u : P)
        exact MulEquiv.symm_apply_apply (h.xi : MulAut P) (u : P)
      right_inv := fun u => by
        apply Subtype.ext
        show h.xi ((h.xi : MulAut P).symm (u : P)) = (u : P)
        exact MulEquiv.apply_symm_apply (h.xi : MulAut P) (u : P)
      map_mul' := fun u v => by
        apply Subtype.ext
        show h.xi ((u : P) * (v : P)) = h.xi (u : P) * h.xi (v : P)
        exact map_mul (h.xi : MulAut P) (u : P) (v : P) }
  have deltaA_xi_aut : ∀ (u : ↥C) (a : ↥A),
      deltaA hAn (xiC h hCinv u) (xiAut a) = xiAut (deltaA hAn u a) := by
    intro u a
    apply Subtype.ext
    show (h.xi (a : P))⁻¹ * ((h.xi (u : P))⁻¹ * (h.xi (a : P) * h.xi (u : P)))
      = h.xi (((a : P))⁻¹ * (((u : P))⁻¹ * ((a : P) * (u : P))))
    simp only [map_mul, map_inv]
  have nuBar_xi : ∀ (u : ↥C) (g : W),
      nuBarF (xiC h hCinv u) (xiW g) = xiW (nuBarF u g) := by
    intro u g
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (N := (powSub A 2).subgroupOf A) g
    change nuBarF (xiC h hCinv u) (xiW (QuotientGroup.mk a))
      = xiW (nuBarF u (QuotientGroup.mk a))
    rw [xiW_mk, nuBar_mk, nuBar_mk]
    change (QuotientGroup.mk (rhoF (deltaToK (xiC h hCinv u) (xiAut a))) : W)
      = xiW (QuotientGroup.mk (rhoF (deltaToK u a)))
    rw [xiW_mk]
    set x : ↥A := rhoF (deltaToK (xiC h hCinv u) (xiAut a)) with hxdef
    set y : ↥A := xiAut (rhoF (deltaToK u a)) with hydef
    refine mk_eq_of_sq_eq_one ?_
    have hx2 : x * x = (deltaA hAn (xiC h hCinv u) (xiAut a))⁻¹ := by
      rw [hxdef, rhoF_spec]
      exact deltaToK_val (xiC h hCinv u) (xiAut a)
    have hy2 : y * y = xiAut ((deltaA hAn u a)⁻¹) := by
      rw [hydef]
      calc xiAut (rhoF (deltaToK u a)) * xiAut (rhoF (deltaToK u a))
          = xiAut (rhoF (deltaToK u a) * rhoF (deltaToK u a)) := (map_mul xiAut _ _).symm
        _ = xiAut ((deltaToK u a).1) := by rw [rhoF_spec]
        _ = xiAut ((deltaA hAn u a)⁻¹) := by rw [deltaToK_val]
    have hxy : x * x = y * y := by
      rw [hx2, hy2, deltaA_xi_aut, map_inv]
    rw [show (x * y⁻¹) * (x * y⁻¹) = (x * x) * (y * y)⁻¹ by
          have hc : y⁻¹ * x = x * y⁻¹ := hcommA y⁻¹ x
          calc (x * y⁻¹) * (x * y⁻¹) = x * ((y⁻¹ * x) * y⁻¹) := by group
            _ = x * ((x * y⁻¹) * y⁻¹) := by rw [hc]
            _ = (x * x) * (y⁻¹ * y⁻¹) := by group
            _ = (x * x) * (y * y)⁻¹ := by rw [mul_inv_rev],
        hxy, mul_inv_cancel]
  have nuBar_one : ∀ g : W, nuBarF 1 g = 1 := by
    intro g
    have h := nuBar_mul (1 : ↥C) 1 g
    rw [mul_one] at h
    have h2 : (nuBarF 1 g)⁻¹ * (nuBarF 1 g)
        = (nuBarF 1 g)⁻¹ * (nuBarF 1 g * nuBarF 1 g) :=
      congrArg (fun t : W => (nuBarF 1 g)⁻¹ * t) h
    rw [inv_mul_cancel, inv_mul_cancel_left] at h2
    exact h2.symm
  -- ### The dichotomy: `ν̄(u)` is trivial or the identity
  have dichotomy : ∀ u : ↥C, (∀ g : W, nuBarF u g = 1) ∨ (∀ g : W, nuBarF u g = g) := by
    haveI hCft : Fintype ↥C := Fintype.ofFinite ↥C
    exact boolean_idempotent_family_mul hW2 xiW htransW nuBarF nuBar_idem
      (fun i j => ⟨i * j, fun g => nuBar_mul i j g⟩)
      ⟨xiCEq.toEquiv, fun i v => nuBar_xi i v⟩
  -- ### `ν̄(u)` trivial implies `u ∈ A`  (Higman's Lemma 2)
  have nuBar_triv_mem : ∀ u : ↥C, (∀ g : W, nuBarF u g = 1) → (u : P) ∈ A := by
    intro u hu
    by_contra huA
    have huinv : ∀ g : W, nuBarF u⁻¹ g = 1 := by
      intro g
      have h := nuBar_mul u u⁻¹ g
      rw [mul_inv_cancel, nuBar_one, hu g, one_mul] at h
      exact h.symm
    have hcomm4 : ∀ a ∈ A, ⁅(u : P), a⁆ ∈ powSub A 4 := by
      intro a ha
      have hd : ((deltaA hAn u⁻¹ ⟨a, ha⟩ : ↥A) : P) ∈ powSub A 4 :=
        (nuBar_zero_iff u⁻¹ ⟨a, ha⟩).mp (huinv (QuotientGroup.mk ⟨a, ha⟩))
      have hδ : ((deltaA hAn u⁻¹ ⟨a, ha⟩ : ↥A) : P) = ⁅(u : P), a⁆ := by
        rw [deltaA_coe, commutatorElement_def]
        have hAu : (u : P) * a * (u : P)⁻¹ ∈ A := hAn.conj_mem a ha (u : P)
        simp only [Subgroup.coe_inv, inv_inv]
        rw [hAb ((u : P) * a * (u : P)⁻¹) hAu (a : P)⁻¹ (A.inv_mem ha)]
        group
      rwa [hδ] at hd
    refine higman_lemma2 h ⟨hAn, hAinv, hAb⟩ hOn hne huA ⟨?_, hcomm4⟩
    exact hC2 (pow_mem_powSub (A := C) u.2)
  -- ### `ν̄(u) = id` implies `a * (u⁻¹ a u) ∈ A⁴` for all `a ∈ A`
  have memK_of_mk_eq : ∀ {x y : ↥A}, (QuotientGroup.mk x : W) = QuotientGroup.mk y →
      x * y⁻¹ ∈ (powSub A 2).subgroupOf A := by
    intro x y h
    rw [← QuotientGroup.eq_one_iff (x * y⁻¹)]
    change (QuotientGroup.mk' ((powSub A 2).subgroupOf A)) (x * y⁻¹) = 1
    rw [map_mul, map_inv]
    have h' : (QuotientGroup.mk' ((powSub A 2).subgroupOf A)) x
        = (QuotientGroup.mk' ((powSub A 2).subgroupOf A)) y := h
    rw [h', mul_inv_cancel]
  have nuBar_id_psi : ∀ u : ↥C, (∀ g : W, nuBarF u g = g) →
      ∀ a ∈ A, a * ((u : P)⁻¹ * a * (u : P)) ∈ powSub A 4 := by
    intro u hu a ha
    set x : ↥A := rhoF (deltaToK u ⟨a, ha⟩) with hxdef
    have hx2 : x * x = (deltaA hAn u ⟨a, ha⟩)⁻¹ := by
      rw [hxdef, rhoF_spec]
      exact deltaToK_val u ⟨a, ha⟩
    have hmk : (QuotientGroup.mk x : W) = QuotientGroup.mk ⟨a, ha⟩ := by
      have h := hu (QuotientGroup.mk ⟨a, ha⟩)
      rw [nuBar_mk] at h
      have h1 : rho (deltaToK u ⟨a, ha⟩) = (QuotientGroup.mk x : W) := rfl
      rwa [h1] at h
    have hc : x * (⟨a, ha⟩ : ↥A)⁻¹ ∈ (powSub A 2).subgroupOf A := memK_of_mk_eq hmk
    have hxp : ((x * (⟨a, ha⟩ : ↥A)⁻¹ : ↥A) : P) ∈ powSub A 2 := (memK_iff).mp hc
    have hsmall : ((((x * (⟨a, ha⟩ : ↥A)⁻¹ : ↥A) : P))⁻¹) ^ 2 ∈ powSub A 4 := by
      have h2 := pow_mem_powSub (A := powSub A 2) (n := 2) (Subgroup.inv_mem _ hxp)
      rwa [powSub_powSub hAb 2 2] at h2
    have hdelta : deltaA hAn u ⟨a, ha⟩ = x⁻¹ * x⁻¹ := by
      calc deltaA hAn u ⟨a, ha⟩ = ((deltaA hAn u ⟨a, ha⟩)⁻¹)⁻¹ := (inv_inv _).symm
        _ = (x * x)⁻¹ := by rw [← hx2]
        _ = x⁻¹ * x⁻¹ := mul_inv_rev x x
    have hcval : ((⟨a, ha⟩ * x⁻¹ : ↥A) : P)
        = (((x * (⟨a, ha⟩ : ↥A)⁻¹ : ↥A) : P))⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv,
        mul_inv_rev, inv_inv]
    have hpsi : (⟨a, ha⟩ * sigmaA hAn u ⟨a, ha⟩ : ↥A)
        = (⟨a, ha⟩ * x⁻¹) * (⟨a, ha⟩ * x⁻¹) := by
      rw [← mul_deltaA hAn hAb u ⟨a, ha⟩, hdelta]
      have hc' : x⁻¹ * (⟨a, ha⟩ : ↥A) = (⟨a, ha⟩ : ↥A) * x⁻¹ := hcommA x⁻¹ ⟨a, ha⟩
      calc (⟨a, ha⟩ : ↥A) * ((⟨a, ha⟩ : ↥A) * (x⁻¹ * x⁻¹))
          = (⟨a, ha⟩ : ↥A) * (((⟨a, ha⟩ : ↥A) * x⁻¹) * x⁻¹) := by group
        _ = (⟨a, ha⟩ : ↥A) * ((x⁻¹ * (⟨a, ha⟩ : ↥A)) * x⁻¹) := by rw [← hc']
        _ = ((⟨a, ha⟩ : ↥A) * x⁻¹) * ((⟨a, ha⟩ : ↥A) * x⁻¹) := by group
    have htarget : ((⟨a, ha⟩ * sigmaA hAn u ⟨a, ha⟩ : ↥A) : P)
        = ((((x * (⟨a, ha⟩ : ↥A)⁻¹ : ↥A) : P))⁻¹) ^ 2 := by
      rw [hpsi, Subgroup.coe_mul, hcval, ← pow_two]
    have hconv : a * ((u : P)⁻¹ * a * (u : P))
        = ((⟨a, ha⟩ * sigmaA hAn u ⟨a, ha⟩ : ↥A) : P) := by
      rw [Subgroup.coe_mul, sigmaA_coe]
    rw [hconv, htarget]
    exact hsmall
  -- ### a choice of `u ∈ C \ A`
  obtain ⟨u0, hu0C, hu0A⟩ : ∃ u : P, u ∈ C ∧ u ∉ A := by
    by_contra hcon
    push Not at hcon
    exact hCA (le_antisymm hAC (fun x hx => hcon x hx))
  have id_u0 : ∀ g : W, nuBarF ⟨u0, hu0C⟩ g = g := by
    rcases dichotomy ⟨u0, hu0C⟩ with h | h
    · exact absurd (nuBar_triv_mem ⟨u0, hu0C⟩ h) hu0A
    · exact h
  have hcoset : ∀ v ∈ C, v ∉ A → v * u0⁻¹ ∈ A := by
    intro v hv hvA
    have id_v : ∀ g : W, nuBarF ⟨v, hv⟩ g = g := by
      rcases dichotomy ⟨v, hv⟩ with h | h
      · exact absurd (nuBar_triv_mem ⟨v, hv⟩ h) hvA
      · exact h
    have hinv : ∀ g : W, nuBarF (⟨u0⁻¹, C.inv_mem hu0C⟩ : ↥C) g = g := by
      intro g
      have h2 := nuBar_mul (⟨u0, hu0C⟩ : ↥C) (⟨u0⁻¹, C.inv_mem hu0C⟩ : ↥C) g
      rw [show (⟨u0, hu0C⟩ : ↥C) * ⟨u0⁻¹, C.inv_mem hu0C⟩ = 1 from mul_inv_cancel _,
        nuBar_one, id_u0 g] at h2
      calc (nuBarF (⟨u0⁻¹, C.inv_mem hu0C⟩ : ↥C)) g
          = 1 * (nuBarF (⟨u0⁻¹, C.inv_mem hu0C⟩ : ↥C)) g := (one_mul _).symm
        _ = (g * g) * (nuBarF (⟨u0⁻¹, C.inv_mem hu0C⟩ : ↥C)) g := by rw [← hW2 g]
        _ = g * (g * (nuBarF (⟨u0⁻¹, C.inv_mem hu0C⟩ : ↥C)) g) := by rw [mul_assoc]
        _ = g * 1 := by rw [← h2]
        _ = g := mul_one g
    have htriv : ∀ g : W, nuBarF (⟨u0⁻¹ * v, C.mul_mem (C.inv_mem hu0C) hv⟩ : ↥C) g = 1 := by
      intro g
      have hmul := nuBar_mul (⟨u0⁻¹, C.inv_mem hu0C⟩ : ↥C) (⟨v, hv⟩ : ↥C) g
      change (nuBarF ((⟨u0⁻¹, C.inv_mem hu0C⟩ : ↥C) * (⟨v, hv⟩ : ↥C))) g = 1
      rw [hmul, hinv g, id_v g, hW2 g]
    have hmemA : u0⁻¹ * v ∈ A :=
      nuBar_triv_mem ⟨u0⁻¹ * v, C.mul_mem (C.inv_mem hu0C) hv⟩ htriv
    have hconj := hAn.conj_mem (u0⁻¹ * v) hmemA u0
    rwa [show u0 * (u0⁻¹ * v) * u0⁻¹ = v * u0⁻¹ by group] at hconj
  have hid : ∀ a ∈ A, a * (u0⁻¹ * a * u0) ∈ powSub A 4 :=
    nuBar_id_psi ⟨u0, hu0C⟩ id_u0
  -- ### contradiction (Higman's final step)
  exact higman_lemma3_final_step h hA hCn hCinv hAC hC2 hOn hne D h3 hq4 hu0C hu0A hcoset hid


end Work.Higman
