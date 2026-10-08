import Mathlib
import Submission.Work.Coprime.All
import Submission.Work.Coprime.exists_invariant_sylow
import Submission.Work.Hering.AppVII.eq_top_of_forall_prime_dvd_sylow_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.AppVII

open scoped Pointwise
open scoped commutatorElement

/-- Conjugation by `a : ↥P` on a subgroup `H ≤ ↥Q`, transported to the ambient group along
`Q.subtype`, agrees with the pointwise conjugation of the ambient subgroup `H.map Q.subtype`. -/
theorem map_conj_eq_map_smul {A : Type*} [Group A] (P Q : Subgroup A) [Q.Normal]
    [MulDistribMulAction ↥P ↥Q]
    (hconj : ∀ (a : ↥P) (q : ↥Q), ((a • q : ↥Q) : A) = (a : A) * (q : A) * (a : A)⁻¹)
    (H : Subgroup ↥Q) (a : ↥P) :
    Subgroup.map (MulAut.conj (a : A)).toMonoidHom (H.map Q.subtype)
      = (a • H).map Q.subtype := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨a • q, Subgroup.smul_mem_pointwise_smul q a H hq, ?_⟩
    show ((a • q : ↥Q) : A) = (MulAut.conj (a : A)) (q : A)
    rw [MulAut.conj_apply, hconj]
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨q', hq', rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists q a H).mp hq
    refine Subgroup.mem_map.mpr ⟨(q' : A), Subgroup.mem_map.mpr ⟨q', hq', rfl⟩, ?_⟩
    show (MulAut.conj (a : A)) (q' : A) = ((a • q' : ↥Q) : A)
    rw [MulAut.conj_apply, hconj]

theorem part1_Q_isPGroup_and_frattini {A : Type*} [Group A] [Finite A] (P Q : Subgroup A)
    (hQn : Q.Normal) (hsup : P ⊔ Q = ⊤) (hinf : P ⊓ Q = ⊥)
    (hPcard : (Nat.card ↥P).Prime) (hpQ : ¬ Nat.card ↥P ∣ Nat.card ↥Q)
    (hnotcent : ⁅P, Q⁆ ≠ ⊥)
    (hcent : ∀ Q' : Subgroup A, Q' ≤ Q → Q' ≠ ⊥ → Q' ≠ Q → ⁅P, Q'⁆ ≤ Q' → ⁅P, Q'⁆ = ⊥) :
    (∃ q : ℕ, q.Prime ∧ IsPGroup q ↥Q) ∧ ⁅P, Q⁆ = Q ∧
      (frattini ↥Q ≤ Subgroup.center ↥Q ∨ IsMulCommutative ↥Q) := by
  haveI : Fact (Nat.card ↥P).Prime := ⟨hPcard⟩
  haveI : Q.Normal := hQn
  have hcop : Nat.Coprime (Nat.card ↥P) (Nat.card ↥Q) := hPcard.coprime_iff_not_dvd.mpr hpQ
  have hsolP : Group.IsSolvable ↥P := by
    haveI : IsCyclic ↥P := isCyclic_of_prime_card (show Nat.card ↥P = Nat.card ↥P from rfl)
    exact Group.isSolvable_of_comm (isMulCommutative_iff.mp inferInstance)
  -- ## Part 2: ⁅P,Q⁆ = Q
  have hPQ : ⁅P, Q⁆ = Q := by
    by_contra hneq
    have hMle : ⁅P, Q⁆ ≤ Q := Subgroup.commutator_le_right P Q
    have hMinv : ⁅P, ⁅P, Q⁆⁆ ≤ ⁅P, Q⁆ := Subgroup.commutator_mono le_rfl hMle
    have hcentM : ⁅P, ⁅P, Q⁆⁆ = ⊥ := hcent ⁅P, Q⁆ hMle hnotcent hneq hMinv
    obtain ⟨a, ha, y, hy, hne⟩ : ∃ a ∈ P, ∃ y ∈ Q, ⁅a, y⁆ ≠ 1 := by
      by_contra h
      push_neg at h
      exact hnotcent (le_bot_iff.mp (Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => by
        rw [Subgroup.mem_bot]; exact h g₁ hg₁ g₂ hg₂))
    set α : MulAut ↥Q := MulAut.conjNormal (H := Q) a with hα
    have hαne : α ≠ 1 := by
      intro h
      have h1 : (α ⟨y, hy⟩ : ↥Q) = ⟨y, hy⟩ := by rw [h]; rfl
      have h2 : a * y * a⁻¹ = y := by
        have h3 := congrArg (Subtype.val) h1
        simpa [hα, MulAut.conjNormal_apply] using h3
      exact hne (by rw [commutatorElement_def, h2, mul_inv_cancel])
    have hapow : a ^ Nat.card ↥P = 1 := by
      have hane : (⟨a, ha⟩ : ↥P) ≠ 1 := by
        intro h
        exact hne (by rw [show a = 1 from Subtype.ext_iff.mp h]; simp)
      have hord : orderOf (⟨a, ha⟩ : ↥P) = Nat.card ↥P := by
        rcases hPcard.eq_one_or_self_of_dvd (orderOf (⟨a, ha⟩ : ↥P))
          (orderOf_dvd_natCard _) with h1 | h1
        · exact absurd (orderOf_eq_one_iff.mp h1) hane
        · exact h1
      have h1 : (⟨a, ha⟩ : ↥P) ^ (Nat.card ↥P) = 1 := by
        rw [← hord]; exact pow_orderOf_eq_one _
      have h2 : ((⟨a, ha⟩ : ↥P) : A) ^ (Nat.card ↥P) = 1 := by
        have h3 := congrArg (fun z : ↥P => (z : A)) h1
        rw [Subgroup.coe_pow, Subgroup.coe_one] at h3
        exact h3
      exact h2
    have hαpow : α ^ Nat.card ↥P = 1 := by
      rw [hα, ← map_pow, hapow, map_one]
    have hordα : orderOf α = Nat.card ↥P := by
      rcases hPcard.eq_one_or_self_of_dvd (orderOf α)
          (orderOf_dvd_iff_pow_eq_one.mpr hαpow) with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hαne
      · exact h1
    have mg_mem : ∀ g : ↥Q, ⁅a, (g : A)⁆ ∈ Q := by
      intro g
      rw [commutatorElement_def]
      exact Q.mul_mem (hQn.conj_mem (g : A) g.2 a) (Q.inv_mem g.2)
    let mg : ↥Q → ↥Q := fun g => ⟨⁅a, (g : A)⁆, mg_mem g⟩
    have hstep : ∀ g : ↥Q, α g = mg g * g := by
      intro g
      apply Subtype.ext
      rw [Subgroup.coe_mul]
      show ((MulAut.conjNormal (H := Q) a) g : A) = ((mg g : ↥Q) : A) * (g : A)
      rw [MulAut.conjNormal_apply]
      change a * (g : A) * a⁻¹ = ⁅a, (g : A)⁆ * (g : A)
      rw [commutatorElement_def]
      group
    have hstep2 : ∀ g : ↥Q, α (mg g) = mg g := by
      intro g
      apply Subtype.ext
      show ((MulAut.conjNormal (H := Q) a) (mg g) : A) = ((mg g : ↥Q) : A)
      rw [MulAut.conjNormal_apply]
      have hmem : (mg g : A) ∈ ⁅P, Q⁆ := Subgroup.commutator_mem_commutator ha g.2
      have hcomm : a * (mg g : A) = (mg g : A) * a :=
        (Subgroup.mem_centralizer_iff.mp
          ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcentM) ha) (mg g : A) hmem).symm
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hiter : ∀ (k : ℕ) (g : ↥Q), (α ^ k) g = (mg g) ^ k * g := by
      intro k
      induction k with
      | zero => intro g; simp
      | succ k ih =>
          intro g
          rw [pow_succ', MulAut.mul_apply, ih g, map_mul, map_pow, hstep2, hstep, pow_succ']
          group
    have hfinal : α ^ (Nat.card ↥(⁅P, Q⁆)) = 1 := by
      apply MulEquiv.ext
      intro g
      rw [hiter, MulAut.one_apply]
      have hmN : (mg g) ^ (Nat.card ↥(⁅P, Q⁆)) = 1 := by
        have hmem : (mg g : A) ∈ ⁅P, Q⁆ := Subgroup.commutator_mem_commutator ha g.2
        have h1 : (⟨(mg g : A), hmem⟩ : ↥(⁅P, Q⁆)) ^ (Nat.card ↥(⁅P, Q⁆)) = 1 :=
          orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard _)
        have h2 := congrArg (fun z : ↥(⁅P, Q⁆) => (z : A)) h1
        simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact h2
      rw [hmN, one_mul]
    have hdvd : Nat.card ↥P ∣ Nat.card ↥(⁅P, Q⁆) := by
      rw [← hordα]
      exact orderOf_dvd_iff_pow_eq_one.mpr hfinal
    exact hpQ (dvd_trans hdvd (Subgroup.card_dvd_of_le hMle))
  -- ## Part 3: Φ(Q) ≤ Z(Q) or Q abelian
  have hPart3 : frattini ↥Q ≤ Subgroup.center ↥Q ∨ IsMulCommutative ↥Q := by
    by_cases hab : IsMulCommutative ↥Q
    · exact Or.inr hab
    · left
      set Φ : Subgroup A := (frattini ↥Q).map Q.subtype with hΦ
      have hΦle : Φ ≤ Q := Subgroup.map_subtype_le _
      have hΦnormal : Φ.Normal := by
        refine ⟨fun x hx g => ?_⟩
        obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
        refine Subgroup.mem_map.mpr ⟨MulAut.conjNormal (H := Q) g z, ?_, ?_⟩
        · have hchar : Subgroup.map (MulAut.conjNormal (H := Q) g).toMonoidHom (frattini ↥Q)
              = frattini ↥Q :=
            Subgroup.characteristic_iff_map_eq.mp (frattini_characteristic (G := ↥Q)) _
          rw [← hchar]
          exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
        · exact MulAut.conjNormal_apply g z
      rcases eq_or_ne Φ ⊥ with hbot | hbot
      · have hfr : frattini ↥Q = ⊥ := by
          have h := hbot
          rw [hΦ] at h
          exact (Subgroup.map_eq_bot_iff_of_injective _ Q.subtype_injective).mp h
        rw [hfr]; exact bot_le
      · have htop : Φ ≠ Q := by
          intro h
          have hcard : Nat.card ↥(frattini ↥Q) = Nat.card ↥Q := by
            rw [← Subgroup.card_map_of_injective Q.subtype_injective (K := frattini ↥Q), ← hΦ, h]
          have hfr : frattini ↥Q = ⊤ := Subgroup.eq_top_of_card_eq _ hcard
          have hng := frattini_nongenerating (G := ↥Q) (K := ⊥) (by rw [bot_sup_eq, hfr])
          haveI : Subsingleton ↥Q := ⟨fun a b => by
            have ha : a = 1 := Subgroup.mem_bot.mp (hng.symm ▸ Subgroup.mem_top a)
            have hb : b = 1 := Subgroup.mem_bot.mp (hng.symm ▸ Subgroup.mem_top b)
            rw [ha, hb]⟩
          exact hab (isMulCommutative_iff.mpr fun a b => Subsingleton.elim (a * b) (b * a))
        have hΦinv : ⁅P, Φ⁆ ≤ Φ := Subgroup.commutator_le_right P Φ
        have hcenΦ : ⁅P, Φ⁆ = ⊥ := hcent Φ hΦle hbot htop hΦinv
        have h1 : ⁅⁅P, Φ⁆, Q⁆ = ⊥ := by rw [hcenΦ, Subgroup.commutator_bot_left]
        have h2 : ⁅⁅Φ, Q⁆, P⁆ = ⊥ := by
          refine le_bot_iff.mp ?_
          calc ⁅⁅Φ, Q⁆, P⁆ ≤ ⁅Φ, P⁆ :=
                Subgroup.commutator_mono (Subgroup.commutator_le_left Φ Q) le_rfl
            _ = ⁅P, Φ⁆ := Subgroup.commutator_comm Φ P
            _ = ⊥ := hcenΦ
        have h3 : ⁅⁅Q, P⁆, Φ⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
        rw [Subgroup.commutator_comm Q P, hPQ] at h3
        have hΦcen : Φ ≤ Subgroup.centralizer (Q : Set A) :=
          (Subgroup.le_centralizer_iff (H := Φ) (K := Q)).mpr
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)
        intro z hz
        rw [Subgroup.mem_center_iff]
        intro w
        have hzΦ : (z : A) ∈ Φ := Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
        have hcomm := Subgroup.mem_centralizer_iff.mp (hΦcen hzΦ) (w : A) w.2
        refine Subtype.ext ?_
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact hcomm
  -- ## Part 1: Q is a q-group
  have hPart1 : ∃ q : ℕ, q.Prime ∧ IsPGroup q ↥Q := by
    by_contra hq
    have hQne : Q ≠ ⊥ := by
      intro hb
      exact hnotcent (by rw [hb]; exact Subgroup.commutator_bot_right P)
    set H : Subgroup ↥Q := Subgroup.comap Q.subtype (Subgroup.centralizer (P : Set A)) with hHdef
    have hHtop : H = ⊤ := by
      refine eq_top_of_forall_prime_dvd_sylow_le H ?_
      intro r hr hrdvd
      haveI : Fact r.Prime := ⟨hr⟩
      letI : MulDistribMulAction ↥P ↥Q :=
        { smul := fun a q => MulAut.conjNormal (H := Q) (a : A) q
          one_smul := fun q => by
            show MulAut.conjNormal (H := Q) ((1 : ↥P) : A) q = q
            rw [Subgroup.coe_one, map_one, MulAut.one_apply]
          mul_smul := fun a b q => by
            show MulAut.conjNormal (H := Q) ((a * b : ↥P) : A) q
              = MulAut.conjNormal (H := Q) (a : A) (MulAut.conjNormal (H := Q) (b : A) q)
            rw [Subgroup.coe_mul, map_mul]; rfl
          smul_one := fun a => by
            show MulAut.conjNormal (H := Q) (a : A) 1 = 1
            rw [map_one]
          smul_mul := fun a x y => by
            show MulAut.conjNormal (H := Q) (a : A) (x * y)
              = MulAut.conjNormal (H := Q) (a : A) x * MulAut.conjNormal (H := Q) (a : A) y
            exact map_mul _ x y }
      have hconj : ∀ (a : ↥P) (q : ↥Q), ((a • q : ↥Q) : A) = (a : A) * (q : A) * (a : A)⁻¹ := by
        intro a q
        show ((MulAut.conjNormal (H := Q) (a : A)) q : A) = _
        rw [MulAut.conjNormal_apply]
      obtain ⟨S, hS⟩ := Work.Coprime.exists_invariant_sylow ↥P hcop (Or.inl hsolP) r
      have hSsub : ∀ a : ↥P, a • (S : Subgroup ↥Q) = (S : Subgroup ↥Q) := by
        intro a
        rw [show a • (S : Subgroup ↥Q) = ((a • S : Sylow r ↥Q) : Subgroup ↥Q) from
          (Sylow.pointwise_smul_def (g := a) (P := S)).symm, hS a]
      have hSconv : ∀ a : ↥P,
          Subgroup.map (MulAut.conj (a : A)).toMonoidHom ((S : Subgroup ↥Q).map Q.subtype)
            = (S : Subgroup ↥Q).map Q.subtype := by
        intro a
        rw [map_conj_eq_map_smul P Q hconj (S : Subgroup ↥Q) a, hSsub a]
      have hSAle : (S : Subgroup ↥Q).map Q.subtype ≤ Q := Subgroup.map_subtype_le _
      have hSAbot : (S : Subgroup ↥Q).map Q.subtype ≠ ⊥ := by
        intro h
        have hSbot : (S : Subgroup ↥Q) = ⊥ :=
          (Subgroup.map_eq_bot_iff_of_injective _ Q.subtype_injective).mp h
        exact Sylow.ne_bot_of_dvd_card S hrdvd (by rw [hSbot])
      have hSAtop : (S : Subgroup ↥Q).map Q.subtype ≠ Q := by
        intro h
        have hcard : Nat.card ↥(S : Subgroup ↥Q) = Nat.card ↥Q := by
          rw [← Subgroup.card_map_of_injective Q.subtype_injective (K := (S : Subgroup ↥Q)), h]
        have hpg : IsPGroup r ↥Q := by
          obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
          exact IsPGroup.of_card (p := r) (n := n) (by rw [← hcard, hn])
        exact hq ⟨r, hr, hpg⟩
      have hSinv : ⁅P, (S : Subgroup ↥Q).map Q.subtype⁆ ≤ (S : Subgroup ↥Q).map Q.subtype := by
        refine Subgroup.commutator_le.mpr ?_
        intro g hg x hx
        have hconj' : g * x * g⁻¹ ∈ (S : Subgroup ↥Q).map Q.subtype := by
          have h1 : (MulAut.conj g) x ∈ Subgroup.map (MulAut.conj g).toMonoidHom
              ((S : Subgroup ↥Q).map Q.subtype) := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
          rw [hSconv ⟨g, hg⟩] at h1
          rwa [MulAut.conj_apply g x] at h1
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ hconj' (Subgroup.inv_mem _ hx)
      have hcenS : ⁅P, (S : Subgroup ↥Q).map Q.subtype⁆ = ⊥ :=
        hcent _ hSAle hSAbot hSAtop hSinv
      have hscen : (S : Subgroup ↥Q).map Q.subtype ≤ Subgroup.centralizer (P : Set A) :=
        Subgroup.le_centralizer_iff.mpr
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcenS)
      refine ⟨S, ?_⟩
      rw [hHdef]
      exact (Subgroup.map_le_iff_le_comap (f := Q.subtype)).mp hscen
    have hQle : Q ≤ Subgroup.centralizer (P : Set A) := by
      intro x hx
      have hmem : (⟨x, hx⟩ : ↥Q) ∈ H := by rw [hHtop]; trivial
      rw [hHdef] at hmem
      exact Subgroup.mem_comap.mp hmem
    have hPle : P ≤ Subgroup.centralizer (Q : Set A) := Subgroup.le_centralizer_iff.mpr hQle
    exact hnotcent (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hPle)
  exact ⟨hPart1, hPQ, hPart3⟩

end Work.Hering.AppVII
