import Mathlib
import Submission.Work.ZassenhausSuzuki.Core
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.SzA.mem_center_iff
import Submission.Work.ZassenhausSuzuki.SzAuto.Vtriv
import Submission.Work.ZassenhausSuzuki.SzAuto.conj_of_complements
import Submission.Work.ZassenhausSuzuki.SzAuto.conj_of_complements_in
import Submission.Work.ZassenhausSuzuki.SzAuto.Vtriv_fixes_center
import Submission.Work.ZassenhausSuzuki.SzAuto.Vtriv_card_pow_two_v2
import Submission.Work.ZassenhausSuzuki.SzAuto.zpowers_lam_eq_top
import Submission.Work.ZassenhausSuzuki.SzAuto.aut_indFst_semilinear
import Submission.Work.ZassenhausSuzuki.SzAuto.not_iterate_eq_of_ringAut_ne_v2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Suzuki 1962, Lemma 6 (conjugacy of the cyclic Hua subgroup)

`A = A(K,θ)` (`K = GF(2^n)`, `θ ≠ 1` of odd order).  Every cyclic `Z' ≤ Aut(A)` of order
`2^n − 1` acting fixed-point-freely on the involutions is `Aut(A)`-conjugate to the standard
torus `Λ = im(hLamHom θ)`.

Structure of the proof (see `suzuki_lemma6_of`).

* `K = Vtriv θ` is the kernel of the action of `Aut(A)` on `A/Z(A) ≅ (K,+)`; it is an abelian
  normal subgroup of `Aut(A)` (`SzAuto/Vtriv.lean` and `Vtriv_abelian` below, using the
  delegated `SzAuto.Vtriv_fixes_center`), of power-of-two order
  (`SzAuto.Vtriv_card_pow_two_v2`).
* `aut_V_core` (below) shows that a generator `z₀` of `Z'` differs from a torus automorphism
  `h_λ` by an element of `K`.  Its two inputs are the delegated
  `SzAuto.aut_indFst_semilinear` (the induced map of an automorphism on the first coordinates is
  semilinear, via the `Hering.AppVIII` classification of `Aut(A)`) and
  `SzAuto.not_iterate_eq_of_ringAut_ne_v2` (a genuinely semilinear map `x ↦ λ·σ x` with
  `σ ≠ 1` has order `< 2ⁿ − 1`); the fixed-point-freeness of `Z'` on the involutions enters as
  `Z' ⊓ K = ⊥` and forces `σ = 1`.
* `SzAuto.zpowers_lam_eq_top` then upgrades `z₀ ≡ h_λ (mod K)` to `Λ = ⟨z₀⟩ · K`.
* Hence `Z'` and `Λ` are complements to the abelian normal Hall subgroup `K` of `Z' ⊔ K`, and
  `SzAuto.conj_of_complements_in` (a relative form of Schur–Zassenhaus, itself reduced to
  `SzAuto.conj_of_complements`) yields the conjugacy.
-/

noncomputable section

set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs

namespace Work.ZassenhausSuzuki

open SzA

variable {n : ℕ} {θ : GaloisField 2 n ≃+* GaloisField 2 n}

/-- The first coordinate of `z ⟨a,0⟩`: the map induced by `z` on the "root coordinates"
`A/Z(A) ≅ (K,+)`. -/
def indA (z : MulAut (SzA (GaloisField 2 n) θ)) (a : GaloisField 2 n) : GaloisField 2 n :=
  (z ⟨a, 0⟩).a

/-- `Vtriv θ` is abelian: its elements are `x ↦ u x * x` with `u` central-valued, and they fix
the centre pointwise (`SzAuto.Vtriv_fixes_center`). -/
theorem Vtriv_abelian (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    (hodd : Odd (orderOf θ)) :
    ∀ a ∈ Vtriv θ, ∀ b ∈ Vtriv θ, a * b = b * a := by
  intro a ha b hb
  have hfix := SzAuto.Vtriv_fixes_center θ hθ hodd
  refine MulEquiv.ext (fun x => ?_)
  have hbZ : b x * x⁻¹ ∈ Subgroup.center (SzA (GaloisField 2 n) θ) := hb x
  have hfixZ : a (b x * x⁻¹) = b x * x⁻¹ := hfix a ha _ hbZ
  have hcomm : (a x * x⁻¹) * (b x * x⁻¹) = (b x * x⁻¹) * (a x * x⁻¹) :=
    Subgroup.mem_center_iff.mp hbZ (a x * x⁻¹)
  calc (a * b) x = a (b x) := by rw [MulAut.mul_apply]
    _ = a ((b x * x⁻¹) * x) := by rw [show (b x * x⁻¹) * x = b x from by group]
    _ = a (b x * x⁻¹) * a x := by rw [map_mul]
    _ = (b x * x⁻¹) * ((a x * x⁻¹) * x) := by
          rw [hfixZ, show (a x * x⁻¹) * x = a x from by group]
    _ = ((b x * x⁻¹) * (a x * x⁻¹)) * x := by group
    _ = ((a x * x⁻¹) * (b x * x⁻¹)) * x := by rw [← hcomm]
    _ = b (a x) := by
          have haZ : a x * x⁻¹ ∈ Subgroup.center (SzA (GaloisField 2 n) θ) := ha x
          have hfixZ' : b (a x * x⁻¹) = a x * x⁻¹ := hfix b hb _ haZ
          have key : b (a x) = ((a x * x⁻¹) * (b x * x⁻¹)) * x := by
            calc b (a x) = b ((a x * x⁻¹) * x) := by
                  rw [show (a x * x⁻¹) * x = a x from by group]
              _ = b (a x * x⁻¹) * b x := by rw [map_mul]
              _ = (a x * x⁻¹) * ((b x * x⁻¹) * x) := by
                    rw [hfixZ', show (b x * x⁻¹) * x = b x from by group]
              _ = ((a x * x⁻¹) * (b x * x⁻¹)) * x := by group
          rw [key]
    _ = (b * a) x := by rw [MulAut.mul_apply]

/-! ## The induced map on the root coordinates -/

/-- `⟨0,b⟩` is central, so its image under any automorphism has vanishing first coordinate. -/
theorem zero_b_a (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    (z : MulAut (SzA (GaloisField 2 n) θ)) (b : GaloisField 2 n) :
    (z ⟨0, b⟩).a = 0 := by
  have h : (⟨0, b⟩ : SzA (GaloisField 2 n) θ) ∈ Subgroup.center (SzA (GaloisField 2 n) θ) :=
    mk_zero_mem_center θ b
  have h2 := mulAut_mem_center z h
  exact (SzA.mem_center_iff θ hθ _).mp h2

/-- The first coordinate of `z x` depends only on the first coordinate of `x`. -/
theorem z_a_decouple (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    (z : MulAut (SzA (GaloisField 2 n) θ)) (a b : GaloisField 2 n) :
    (z ⟨a, b⟩).a = (z ⟨a, 0⟩).a := by
  have h1 : (⟨a, b⟩ : SzA (GaloisField 2 n) θ) = ⟨a, 0⟩ * ⟨0, b⟩ := by ext <;> simp
  rw [h1, map_mul, SzA.mul_a, zero_b_a θ hθ z b, add_zero]

/-- `indA` is multiplicative as a map on automorphisms. -/
theorem indA_mul (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    (z₁ z₂ : MulAut (SzA (GaloisField 2 n) θ)) (a : GaloisField 2 n) :
    indA (z₁ * z₂) a = indA z₁ (indA z₂ a) := by
  have hz₂ : z₂ ⟨a, 0⟩ = (⟨indA z₂ a, (z₂ ⟨a, 0⟩).b⟩ : SzA (GaloisField 2 n) θ) := by ext <;> rfl
  show (z₁ (z₂ ⟨a, 0⟩)).a = indA z₁ (indA z₂ a)
  rw [hz₂]
  exact z_a_decouple θ hθ z₁ (indA z₂ a) (z₂ ⟨a, 0⟩).b

theorem indA_one (θ : GaloisField 2 n ≃+* GaloisField 2 n) (a : GaloisField 2 n) :
    indA (1 : MulAut (SzA (GaloisField 2 n) θ)) a = a := rfl

/-- Iterated form of `indA_mul`. -/
theorem indA_pow (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    (z : MulAut (SzA (GaloisField 2 n) θ)) (m : ℕ) (a : GaloisField 2 n) :
    indA (z ^ m) a = (indA z)^[m] a := by
  induction m generalizing a with
  | zero => simp [indA_one]
  | succ m ih =>
    rw [pow_succ', indA_mul θ hθ z (z ^ m) a, ih a, Function.iterate_succ_apply']

/-- An automorphism inducing the identity on the root coordinates lies in `Vtriv θ`. -/
theorem mem_Vtriv_of_indA_eq_id (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    (z : MulAut (SzA (GaloisField 2 n) θ)) (h : ∀ a, indA z a = a) : z ∈ Vtriv θ := by
  intro x
  rw [SzA.mem_center_iff θ hθ]
  obtain ⟨a, b⟩ := x
  show (z ⟨a, b⟩ * (⟨a, b⟩ : SzA (GaloisField 2 n) θ)⁻¹).a = 0
  rw [SzA.mul_a, SzA.inv_a, z_a_decouple θ hθ z a b]
  show (z ⟨a, 0⟩).a + -a = 0
  rw [show (z ⟨a, 0⟩).a = a from h a]
  exact add_neg_cancel a

/-- **The core of Suzuki's Lemma 6.**  An automorphism `z` of `A(K,θ)` of order `2ⁿ - 1` whose
cyclic group meets `Vtriv θ` trivially differs from a torus automorphism `h_λ` by an element of
`Vtriv θ`.

The induced map on the root coordinates is semilinear,
`(z ⟨a,0⟩).a = λ · σ a` (`SzAuto.aut_indFst_semilinear`, proved from the `Hering.AppVIII`
classification of `Aut(A)`), and the order computation
`SzAuto.not_iterate_eq_of_ringAut_ne_v2` — a genuine semilinear map `x ↦ λ · σ x` with `σ ≠ 1`
has order `< 2ⁿ - 1` — forces `σ = 1`, where the hypothesis `⟨z⟩ ⊓ Vtriv θ = ⊥` is used. -/
theorem aut_V_core (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hθ : θ ≠ 1)
    (hodd : Odd (orderOf θ)) (z : MulAut (SzA (GaloisField 2 n) θ))
    (hz : orderOf z = 2 ^ n - 1) (hdisj : Subgroup.zpowers z ⊓ Vtriv θ = ⊥) :
    ∃ lam : (GaloisField 2 n)ˣ, ∀ x : SzA (GaloisField 2 n) θ,
      z x * (SzA.hLam θ (lam : GaloisField 2 n) x)⁻¹
        ∈ Subgroup.center (SzA (GaloisField 2 n) θ) := by
  obtain ⟨lam, σ, hσ⟩ := SzAuto.aut_indFst_semilinear θ hθ hodd z
  have hn : 1 ≤ n := by
    have hpos := orderOf_pos z
    rw [hz] at hpos
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hpos
    · exact h
  have hfun : indA z = fun y : GaloisField 2 n => (lam : GaloisField 2 n) * σ y := funext hσ
  -- the semilinear part of the induced map must be trivial
  have hσ1 : σ = 1 := by
    by_contra hne
    have hnot := SzAuto.not_iterate_eq_of_ringAut_ne_v2 hn lam σ hne
    apply hnot
    intro x
    refine ⟨?_, ?_⟩
    · rw [← hfun]
      rw [← indA_pow θ hθ z (2 ^ n - 1) x,
        show z ^ (2 ^ n - 1) = 1 by rw [← hz]; exact pow_orderOf_eq_one z, indA_one]
    · intro m hm0 hmlt
      by_contra hcon
      push_neg at hcon
      have hid : indA (z ^ m) = id := by
        funext a
        rw [indA_pow θ hθ z m a, hfun]
        exact hcon a
      have hmem : z ^ m ∈ Vtriv θ :=
        mem_Vtriv_of_indA_eq_id θ hθ (z ^ m) (fun a => congrFun hid a)
      have hmem2 : z ^ m ∈ Subgroup.zpowers z ⊓ Vtriv θ :=
        ⟨Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), by simp⟩, hmem⟩
      rw [hdisj] at hmem2
      have hz1 : z ^ m = 1 := by simpa using hmem2
      have hdiv : orderOf z ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hz1
      rw [hz] at hdiv
      have hle : 2 ^ n - 1 ≤ m := Nat.le_of_dvd hm0 hdiv
      omega
  refine ⟨lam, ?_⟩
  intro x
  rw [SzA.mem_center_iff θ hθ]
  obtain ⟨a, b⟩ := x
  show (z ⟨a, b⟩ * (SzA.hLam θ (lam : GaloisField 2 n) ⟨a, b⟩)⁻¹).a = 0
  rw [SzA.mul_a, SzA.inv_a, SzA.hLam_a, z_a_decouple θ hθ z a b]
  show (z ⟨a, 0⟩).a + -(↑lam * a) = 0
  rw [hσ a, hσ1]
  show (↑lam * a) + -((↑lam : GaloisField 2 n) * a) = 0
  ring

/-- **Assembly.**  `suzuki_lemma6` follows from the core `aut_V_core` and the two inputs
`hfix` (`Vtriv θ` fixes the centre) and `hpow` (`Vtriv θ` has power-of-two order). -/
theorem suzuki_lemma6_of
    (hcore : ∀ (n : ℕ) (θ : GaloisField 2 n ≃+* GaloisField 2 n), θ ≠ 1 → Odd (orderOf θ) →
      ∀ z : MulAut (SzA (GaloisField 2 n) θ), orderOf z = 2 ^ n - 1 →
      Subgroup.zpowers z ⊓ Vtriv θ = ⊥ →
      ∃ lam : (GaloisField 2 n)ˣ, ∀ x : SzA (GaloisField 2 n) θ,
        z x * (SzA.hLam θ (lam : GaloisField 2 n) x)⁻¹
          ∈ Subgroup.center (SzA (GaloisField 2 n) θ))
    (hfix : ∀ (n : ℕ) (θ : GaloisField 2 n ≃+* GaloisField 2 n), θ ≠ 1 → Odd (orderOf θ) →
      ∀ φ ∈ Vtriv θ, ∀ z ∈ Subgroup.center (SzA (GaloisField 2 n) θ), φ z = z)
    (hpow : ∀ (n : ℕ) (θ : GaloisField 2 n ≃+* GaloisField 2 n), θ ≠ 1 → Odd (orderOf θ) →
      ∃ m, Nat.card ↥(Vtriv θ) = 2 ^ m) :
    Work.ZassenhausSuzuki.SuzukiLemma6Prop := by
  intro n θ hθ hodd Z' hcyc hcard hfpf
  classical
  obtain ⟨z₀, hz₀⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Z')
  have hz₀' : orderOf (z₀ : MulAut (SzA (GaloisField 2 n) θ)) = 2 ^ n - 1 := by
    rw [Subgroup.orderOf_coe, hz₀, hcard]
  have hn : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Nat.sub_self] at hz₀'
    have hpos := orderOf_pos (z₀ : MulAut (SzA (GaloisField 2 0) θ))
    omega
  set K : Subgroup (MulAut (SzA (GaloisField 2 n) θ)) := Vtriv θ with hK
  have hKnorm : K.Normal := by rw [hK]; exact Vtriv_normal θ
  have hZ' : Z' = Subgroup.zpowers (z₀ : MulAut (SzA (GaloisField 2 n) θ)) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem z₀.2) ?_
    rw [Nat.card_zpowers, hz₀', ← hcard]
  -- `Z' ⊓ Vtriv θ = ⊥`: an element of `Vtriv` fixes the involution `⟨0,1⟩`, and `Z'` acts
  -- fixed-point-freely on the involutions.
  have hdisj : Subgroup.zpowers (z₀ : MulAut (SzA (GaloisField 2 n) θ)) ⊓ Vtriv θ = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have hxZ' : x ∈ Z' := by rw [hZ']; exact hx1
    have hfixx : x (⟨0, 1⟩ : SzA (GaloisField 2 n) θ) = ⟨0, 1⟩ :=
      Vtriv_fixes_involution θ hθ hx2
    by_contra hne
    have hinv : (⟨0, 1⟩ : SzA (GaloisField 2 n) θ) * ⟨0, 1⟩ = 1 := by
      ext <;> simp [CharTwo.add_self_eq_zero]
    have h1 : (⟨0, 1⟩ : SzA (GaloisField 2 n) θ) = 1 := hfpf x hxZ' hne ⟨0, 1⟩ hinv hfixx
    have : (1 : GaloisField 2 n) = 0 := by simpa using congrArg SzA.b h1
    exact one_ne_zero this
  obtain ⟨lam, hlam⟩ := hcore n θ hθ hodd (z₀ : MulAut _) hz₀' hdisj
  set Λ : Subgroup (MulAut (SzA (GaloisField 2 n) θ)) := (SzA.hLamHom θ).range with hΛ
  have hfix' : ∀ φ ∈ K, ∀ z ∈ Subgroup.center (SzA (GaloisField 2 n) θ), φ z = z := by
    rw [hK]; exact hfix n θ hθ hodd
  have hpow' : ∃ m, Nat.card ↥K = 2 ^ m := by rw [hK]; exact hpow n θ hθ hodd
  -- the torus element `h_λ` generates the whole torus `Λ ≅ Kˣ`
  have hgen : Subgroup.zpowers lam = ⊤ :=
    SzAuto.zpowers_lam_eq_top θ hn _ hz₀' hdisj lam hlam
  have hΛ_eq : Λ = Subgroup.zpowers (SzA.hLamHom θ lam) := by
    rw [hΛ, MonoidHom.range_eq_map, ← hgen, MonoidHom.map_zpowers]
  have hz₀_memK : (z₀ : MulAut _) * (SzA.hLamHom θ lam)⁻¹ ∈ K := by
    rw [hK]
    intro x
    have h := hlam ((SzA.hLamHom θ lam)⁻¹ x)
    have h2 : SzA.hLamHom θ lam ((SzA.hLamHom θ lam)⁻¹ x) = x := by
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    rw [MulAut.mul_apply]
    rw [show SzA.hLam θ (lam : GaloisField 2 n) ((SzA.hLamHom θ lam)⁻¹ x) = x from by
      rw [← SzA.hLamHom_apply]; exact h2] at h
    exact h
  have hhlam_memΛ : SzA.hLamHom θ lam ∈ Λ := by rw [hΛ]; exact ⟨lam, rfl⟩
  have hKconj : (SzA.hLamHom θ lam)⁻¹ * (z₀ : MulAut _) ∈ K := by
    have hc := hKnorm.conj_mem ((z₀ : MulAut _) * (SzA.hLamHom θ lam)⁻¹) hz₀_memK
      (SzA.hLamHom θ lam)⁻¹
    rwa [show (SzA.hLamHom θ lam)⁻¹ * ((z₀ : MulAut _) * (SzA.hLamHom θ lam)⁻¹)
        * ((SzA.hLamHom θ lam)⁻¹)⁻¹ = (SzA.hLamHom θ lam)⁻¹ * (z₀ : MulAut _) from by group] at hc
  have hz₀_sup : (z₀ : MulAut _) ∈ Λ ⊔ K := by
    have h : (SzA.hLamHom θ lam) * ((SzA.hLamHom θ lam)⁻¹ * (z₀ : MulAut _)) ∈ Λ ⊔ K :=
      Subgroup.mul_mem_sup hhlam_memΛ hKconj
    rwa [show (SzA.hLamHom θ lam) * ((SzA.hLamHom θ lam)⁻¹ * (z₀ : MulAut _))
        = (z₀ : MulAut _) from by group] at h
  have hhlam_sup : SzA.hLamHom θ lam ∈ Subgroup.zpowers (z₀ : MulAut _) ⊔ K :=
    Subgroup.mem_sup_of_normal_right.mpr
      ⟨z₀, Subgroup.mem_zpowers _, ((SzA.hLamHom θ lam)⁻¹ * (z₀ : MulAut _))⁻¹,
        Subgroup.inv_mem K hKconj, by group⟩
  -- `Λ ≤ Z' ⊔ K` because `λ` generates `Kˣ`, and `Z' ≤ Λ ⊔ K` because `z₀ ∈ Λ · K`
  have hE : Λ ≤ Z' ⊔ K := by
    rw [hΛ_eq]
    refine Subgroup.zpowers_le.mpr ?_
    rw [hZ']
    exact hhlam_sup
  have hZ'le : Z' ≤ Λ ⊔ K := by
    rw [hZ']
    exact Subgroup.zpowers_le.mpr hz₀_sup
  have hEeq : Z' ⊔ K = Λ ⊔ K :=
    le_antisymm (sup_le hZ'le le_sup_right) (sup_le hE le_sup_right)
  have hinfZ' : Z' ⊓ K = ⊥ := by rw [hZ', hK]; exact hdisj
  -- `Λ ⊓ Vtriv θ = ⊥`: an element of `Λ` acting trivially on `A/Z(A)` is multiplication by `1`
  have hinfΛ : Λ ⊓ K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxΛ, hxK⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨μ, rfl⟩ := hxΛ
    rw [hK] at hxK
    have hmem : SzA.hLamHom θ μ (⟨1, 0⟩ : SzA (GaloisField 2 n) θ)
        * (⟨1, 0⟩ : SzA (GaloisField 2 n) θ)⁻¹
        ∈ Subgroup.center (SzA (GaloisField 2 n) θ) := hxK _
    have ha := (SzA.mem_center_iff θ hθ _).mp hmem
    have hsum : (μ : GaloisField 2 n) + 1 = 0 := by
      simpa [SzA.hLamHom_apply, SzA.hLam, CharTwo.neg_eq] using ha
    have hneg : (-1 : GaloisField 2 n) = 1 := CharTwo.neg_eq 1
    have hμ : (μ : GaloisField 2 n) = 1 := by
      have h2 := eq_neg_of_add_eq_zero_left hsum
      rwa [hneg] at h2
    have hμu : μ = 1 := Units.ext hμ
    rw [hμu, map_one]
  -- `|K| = 2^m` is coprime to `|Z'| = 2^n - 1`
  have hcop : Nat.Coprime (Nat.card K) (Nat.card Z') := by
    obtain ⟨m, hm⟩ := hpow'
    rw [hm, hcard]
    have hodd2 : Odd (2 ^ n - 1) := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      refine ⟨2 ^ k - 1, ?_⟩
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
      rw [pow_succ]
      omega
    exact Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hodd2)
  -- Schur–Zassenhaus conjugacy of the two complements `Z'` and `Λ` of `K` in `E = Z' ⊔ K`
  obtain ⟨k, _hk, hconj⟩ := SzAuto.conj_of_complements_in K Z' Λ (Z' ⊔ K)
    le_sup_right le_sup_left hE
    (by rw [hK]; exact Vtriv_abelian θ hθ hodd)
    (fun g _ k hk => hKnorm.conj_mem k hk g)
    hcop rfl hinfZ' hEeq.symm hinfΛ
  exact ⟨k, hconj⟩

end Work.ZassenhausSuzuki

namespace Work.ZassenhausSuzuki

open SzA

/-- **Suzuki 1962, Lemma 6.**

Assembled from `suzuki_lemma6_of` with the three inputs `aut_V_core` (an automorphism of order
`q - 1` acting fixed-point-freely on the involutions is a torus automorphism modulo `Vtriv`),
`SzAuto.Vtriv_fixes_center`, and `SzAuto.Vtriv_card_pow_two_v2`. -/
theorem suzuki_lemma6 : Work.ZassenhausSuzuki.SuzukiLemma6Prop :=
  suzuki_lemma6_of
    (fun n θ hθ hodd z hz hdisj => aut_V_core θ hθ hodd z hz hdisj)
    (fun n θ hθ hodd => SzAuto.Vtriv_fixes_center θ hθ hodd)
    (fun n θ hθ hodd => SzAuto.Vtriv_card_pow_two_v2 θ hθ hodd)

end Work.ZassenhausSuzuki
