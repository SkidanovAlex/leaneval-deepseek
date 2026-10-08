import Mathlib
import Submission.Work.Grun.Basic
import Submission.Work.Grun.Diag
import Submission.Work.Grun.Hyp
import Submission.Work.Grun.prod_theta_conj_eq_iterComm_fixed

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Classical Pointwise commutatorElement

namespace Work.Grun

lemma prod_rec_nat {A : Type*} [CommGroup A] (c : ℕ → A) (s k : ℕ) :
    (∏ j ∈ Finset.range (s+2), c (k - j) ^ binomExp (s+1) j)
      = (∏ j ∈ Finset.range (s+1), c (k - j) ^ binomExp s j)
        * (∏ j ∈ Finset.range (s+1), c (k - (j+1)) ^ binomExp s j)⁻¹ := by
  have hL : (∏ j ∈ Finset.range (s+2), c (k - j) ^ binomExp (s+1) j)
      = (∏ j ∈ Finset.range (s+1), c (k - (j+1)) ^ binomExp (s+1) (j+1)) * c k := by
    rw [Finset.prod_range_succ']
    simp only [binomExp_zero_right, Nat.sub_zero, zpow_one]
  have hkey : (∏ j ∈ Finset.range (s+1), c (k - (j+1)) ^ binomExp (s+1) (j+1))
      = (∏ j ∈ Finset.range (s+1), c (k - (j+1)) ^ binomExp s (j+1))
        * (∏ j ∈ Finset.range (s+1), c (k - (j+1)) ^ binomExp s j)⁻¹ := by
    have hc := Finset.prod_congr (rfl : Finset.range (s+1) = Finset.range (s+1))
      (fun j (_ : j ∈ Finset.range (s+1)) => by
        show c (k - (j+1)) ^ binomExp (s+1) (j+1)
            = c (k - (j+1)) ^ binomExp s (j+1) * (c (k - (j+1)) ^ binomExp s j)⁻¹
        rw [binomExp_succ_succ]
        rw [show binomExp s (j+1) - binomExp s j = binomExp s (j+1) + (-(binomExp s j)) by ring]
        rw [zpow_add, zpow_neg])
    rw [hc, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have hA : (∏ j ∈ Finset.range (s+1), c (k - (j+1)) ^ binomExp s (j+1))
      = ∏ j ∈ Finset.range s, c (k - (j+1)) ^ binomExp s (j+1) := by
    rw [Finset.prod_range_succ, binomExp_eq_zero_of_lt s (s+1) (Nat.lt_succ_self s),
      zpow_zero, mul_one]
  have hB : (∏ j ∈ Finset.range s, c (k - (j+1)) ^ binomExp s (j+1)) * c k
      = ∏ j ∈ Finset.range (s+1), c (k - j) ^ binomExp s j := by
    rw [Finset.prod_range_succ', binomExp_zero_right, Nat.sub_zero, zpow_one]
  rw [hL, hkey, hA, mul_assoc, mul_comm _ (c k), ← mul_assoc, hB]


/-- `θ` of a conjugate of `u` only depends (in the commutative target) on `u` when the representative
is a representative of a fixed coset.  Helper for the cycle computation. -/
lemma theta_diagFactor_eq_of_rep {G : Type*} [Group G] {H : Subgroup G} {A : Type*} [CommGroup A]
    (θ : H →* A) {u x : G} (hx : x⁻¹ * u * x ∈ H) {γ : G ⧸ H} (hγ : u • γ = γ)
    (hrep : (x : G ⧸ H) = γ) :
    θ ⟨x⁻¹ * u * x, hx⟩ = θ (diagFactor H u ⟨γ, mem_fixedCosets.mpr hγ⟩) := by
  have hmem : γ.out⁻¹ * x ∈ H :=
    QuotientGroup.eq.mp ((Quotient.out_eq' γ).trans hrep.symm)
  have hx_eq : x = γ.out * (γ.out⁻¹ * x) := by group
  have key : x⁻¹ * u * x = (γ.out⁻¹ * x)⁻¹ * (γ.out⁻¹ * u * γ.out) * (γ.out⁻¹ * x) := by
    rw [hx_eq]; group
  have hcoe : (⟨x⁻¹ * u * x, hx⟩ : H)
      = (⟨γ.out⁻¹ * x, hmem⟩ : H)⁻¹ * diagFactor H u ⟨γ, mem_fixedCosets.mpr hγ⟩
        * ⟨γ.out⁻¹ * x, hmem⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_diagFactor]
    rw [key]
  rw [hcoe, map_mul, map_mul, map_inv]
  simp [mul_comm]

/-- Hall's cycle computation for the diagonal product along one `z`-cycle of fixed cosets. -/
lemma cycle_prod_eq_one {G : Type*} [Group G] {H : Subgroup G} {p : ℕ} [Fact p.Prime]
    {A : Type*} [CommGroup A] (θ : H →* A) (hexp : ∀ a : A, a ^ p = 1)
    {u z : G} (hfin : iterComm (p - 1) u z = 1)
    (γ : G ⧸ H) (hfix : ∀ k : ℕ, u • (z ^ k • γ) = z ^ k • γ) :
    (∏ k ∈ Finset.range p, θ (diagFactor H u ⟨z ^ k • γ, mem_fixedCosets.mpr (hfix k)⟩)) = 1 := by
  classical
  set x : G := γ.out with hxdef
  have hxout : (x : G ⧸ H) = γ := Quotient.out_eq' γ
  have hcoset : ∀ k : ℕ, ((z ^ k * x : G) : G ⧸ H) = z ^ k • γ := by
    intro k
    induction k with
    | zero => simpa using hxout
    | succ n ih =>
        rw [pow_succ', mul_assoc]
        rw [show ((z * (z ^ n * x) : G) : G ⧸ H) = z • ((z ^ n * x : G) : G ⧸ H) by
          rw [MulAction.Quotient.smul_mk, smul_eq_mul]]
        rw [ih, ← mul_smul, ← pow_succ']
  have hXk : ∀ k : ℕ, 1 ≤ k → z ^ k * x = z * (z ^ (k-1) * x) := by
    intro k hk
    conv_lhs => rw [show k = (k-1)+1 from (Nat.sub_add_cancel hk).symm, pow_succ']
    rw [mul_assoc]
  have hrec : ∀ s k : ℕ, 1 ≤ k →
      (z ^ k * x)⁻¹ * iterComm (s+1) u z * (z ^ k * x)
        = ((z ^ k * x)⁻¹ * iterComm s u z * (z ^ k * x))
          * ((z ^ (k-1) * x)⁻¹ * iterComm s u z * (z ^ (k-1) * x))⁻¹ := by
    intro s k hk
    rw [iterComm_succ, commutatorElement_def, hXk k hk]
    group
  have memH : ∀ s k : ℕ, s ≤ k → k < p →
      (z ^ k * x)⁻¹ * iterComm s u z * (z ^ k * x) ∈ H := by
    intro s
    induction s with
    | zero =>
        intro k _ hk
        have h := hfix k
        rw [← hcoset k] at h
        have h2 : ((z ^ k * x : G) : G ⧸ H) = ((u * (z ^ k * x) : G) : G ⧸ H) := by
          rw [← h]
          rw [show u • ((z^k * x : G) : G ⧸ H) = (u * (z ^ k * x) : G ⧸ H) by
            rw [MulAction.Quotient.smul_mk, smul_eq_mul]]
        have hmem := QuotientGroup.eq.mp h2
        simpa [iterComm_zero, mul_assoc] using hmem
    | succ n ih =>
        intro k hk hkp
        have hk1 : 1 ≤ k := by omega
        rw [hrec n k hk1]
        exact H.mul_mem (ih k (by omega) hkp) (H.inv_mem (ih (k-1) (by omega) (by omega)))
  have formula : ∀ s k : ℕ, ∀ (hs : s ≤ k) (hk : k < p),
      θ ⟨(z ^ k * x)⁻¹ * iterComm s u z * (z ^ k * x), memH s k hs hk⟩
        = ∏ j ∈ Finset.range (s+1),
            θ ⟨(z ^ (k - j) * x)⁻¹ * u * (z ^ (k - j) * x),
                memH 0 (k - j) (Nat.zero_le _) (by omega)⟩ ^ binomExp s j := by
    intro s
    induction s with
    | zero =>
        intro k hs hk
        rw [Finset.prod_range_succ']
        simp only [Finset.prod_range_zero, one_mul, binomExp_zero_right, zpow_one,
          Nat.sub_zero, iterComm_zero]
    | succ n ih =>
        intro k hs hk
        have hk1 : 1 ≤ k := by omega
        let c : ℕ → A := fun m => if hm : m < p then
          θ ⟨(z ^ m * x)⁻¹ * u * (z ^ m * x), memH 0 m (Nat.zero_le _) hm⟩ else 1
        have hc : ∀ m (hm : m < p), c m = θ ⟨(z ^ m * x)⁻¹ * u * (z ^ m * x),
            memH 0 m (Nat.zero_le _) hm⟩ := by
          intro m hm
          simp only [c, dif_pos hm]
        have hR : (∏ j ∈ Finset.range (n+2),
              θ ⟨(z ^ (k - j) * x)⁻¹ * u * (z ^ (k - j) * x),
                  memH 0 (k - j) (Nat.zero_le _) (by omega)⟩ ^ binomExp (n+1) j)
            = ∏ j ∈ Finset.range (n+2), c (k - j) ^ binomExp (n+1) j := by
          refine Finset.prod_congr rfl fun j hj => ?_
          rw [hc (k - j) (by omega)]
        have hstep : θ ⟨(z ^ k * x)⁻¹ * iterComm (n+1) u z * (z ^ k * x), memH (n+1) k hs hk⟩
            = (∏ j ∈ Finset.range (n+1), θ ⟨(z ^ (k - j) * x)⁻¹ * u * (z ^ (k - j) * x),
                  memH 0 (k - j) (Nat.zero_le _) (by omega)⟩ ^ binomExp n j)
              * (∏ j ∈ Finset.range (n+1), θ ⟨(z ^ (k - 1 - j) * x)⁻¹ * u * (z ^ (k - 1 - j) * x),
                  memH 0 (k - 1 - j) (Nat.zero_le _) (by omega)⟩ ^ binomExp n j)⁻¹ := by
          rw [show (⟨(z ^ k * x)⁻¹ * iterComm (n+1) u z * (z ^ k * x), memH (n+1) k hs hk⟩ : H)
                = ⟨(z ^ k * x)⁻¹ * iterComm n u z * (z ^ k * x), memH n k (by omega) hk⟩
                  * (⟨(z ^ (k-1) * x)⁻¹ * iterComm n u z * (z ^ (k-1) * x),
                      memH n (k-1) (by omega) (by omega)⟩)⁻¹ from by
              apply Subtype.ext
              simp only [Subgroup.coe_mul, Subgroup.coe_inv]
              exact hrec n k hk1]
          rw [map_mul, map_inv, ih k (by omega) hk, ih (k-1) (by omega) (by omega)]
        rw [hstep, hR, prod_rec_nat c n k]
        congr 1
        · refine Finset.prod_congr rfl fun j hj => ?_
          rw [hc (k-j) (by omega)]
        · congr 1
          refine Finset.prod_congr rfl fun j hj => ?_
          rw [show k - (j + 1) = k - 1 - j by omega, hc (k-1-j) (by omega)]
  -- relate diagFactor to the Vm 0 elements
  have hdiag : ∀ k (hk : k < p),
      θ (diagFactor H u ⟨z ^ k • γ, mem_fixedCosets.mpr (hfix k)⟩)
      = θ ⟨(z ^ k * x)⁻¹ * u * (z ^ k * x), memH 0 k (Nat.zero_le _) hk⟩ :=
    fun k hk => (theta_diagFactor_eq_of_rep θ (memH 0 k (Nat.zero_le _) hk) (hfix k) (hcoset k)).symm
  let f : ℕ → A := fun k => if hk : k < p then
    θ ⟨(z ^ k * x)⁻¹ * u * (z ^ k * x), memH 0 k (Nat.zero_le _) hk⟩ else 1
  have hf : ∀ k (hk : k < p), f k = θ ⟨(z ^ k * x)⁻¹ * u * (z ^ k * x),
      memH 0 k (Nat.zero_le _) hk⟩ := by
    intro k hk; simp only [f, dif_pos hk]
  have hprod1 : (∏ k ∈ Finset.range p, θ (diagFactor H u ⟨z ^ k • γ, mem_fixedCosets.mpr (hfix k)⟩))
      = ∏ k ∈ Finset.range p, f k := by
    refine Finset.prod_congr rfl (fun k hk => ?_)
    rw [hf k (Finset.mem_range.mp hk)]
    exact hdiag k (Finset.mem_range.mp hk)
  have hp1 : p - 1 < p := Nat.sub_one_lt (Fact.out : p.Prime).ne_zero
  have hzero : θ ⟨(z ^ (p-1) * x)⁻¹ * iterComm (p-1) u z * (z ^ (p-1) * x),
      memH (p-1) (p-1) (le_refl _) hp1⟩ = 1 := by
    rw [show (⟨(z ^ (p-1) * x)⁻¹ * iterComm (p-1) u z * (z ^ (p-1) * x),
        memH (p-1) (p-1) (le_refl _) hp1⟩ : H) = 1 from by
      apply Subtype.ext
      simp [hfin]]
    exact map_one θ
  have hform := formula (p - 1) (p - 1) (le_refl _) hp1
  have hpow : (∏ j ∈ Finset.range p, θ ⟨(z ^ (p-1-j) * x)⁻¹ * u * (z ^ (p-1-j) * x),
        memH 0 (p-1-j) (Nat.zero_le _) (by omega)⟩ ^ binomExp (p-1) j)
      = ∏ j ∈ Finset.range p, θ ⟨(z ^ (p-1-j) * x)⁻¹ * u * (z ^ (p-1-j) * x),
        memH 0 (p-1-j) (Nat.zero_le _) (by omega)⟩ := by
    refine Finset.prod_congr rfl (fun j hj => ?_)
    exact zpow_eq_self_of_modEq hexp
      (binomExp_modEq_one j (Nat.le_sub_one_of_lt (Finset.mem_range.mp hj))) _
  have hfprod : (∏ j ∈ Finset.range p, θ ⟨(z ^ (p-1-j) * x)⁻¹ * u * (z ^ (p-1-j) * x),
        memH 0 (p-1-j) (Nat.zero_le _) (by omega)⟩)
      = ∏ j ∈ Finset.range p, f (p-1-j) := by
    refine Finset.prod_congr rfl (fun j hj => ?_)
    rw [hf (p-1-j) (by omega)]
  have hs1 : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_le
  have hform' : (∏ j ∈ Finset.range p, θ ⟨(z ^ (p-1-j) * x)⁻¹ * u * (z ^ (p-1-j) * x),
        memH 0 (p-1-j) (Nat.zero_le _) (by omega)⟩ ^ binomExp (p-1) j) = 1 := by
    rw [show Finset.range p = Finset.range (p - 1 + 1) by rw [hs1]]
    exact hform.symm.trans hzero
  have hone : (∏ k ∈ Finset.range p, f k) = 1 := by
    rw [← Finset.prod_range_reflect f p, ← hfprod, ← hpow]
    exact hform'
  rw [hprod1, hone]


/-- A finite `σ`-invariant set all of whose `σ`-orbits have size `p`, and on which the product of `g`
over each orbit is `1`, has product `1`. -/
lemma free_prod_eq_one {α : Type*} [DecidableEq α] {A : Type*} [CommGroup A] {p : ℕ}
    [Fact p.Prime] (σ : α → α) (g : α → A) (T : Finset α)
    (hT : ∀ a ∈ T, σ a ∈ T)
    (hp : ∀ a ∈ T, (σ^[p]) a = a)
    (hnf : ∀ a ∈ T, ∀ k, 0 < k → k < p → (σ^[k]) a ≠ a)
    (hprod : ∀ a ∈ T, ∏ k ∈ Finset.range p, g ((σ^[k]) a) = 1) :
    ∏ a ∈ T, g a = 1 := by
  have hp1le : 1 ≤ p := (Fact.out : p.Prime).one_le
  refine Finset.strongInductionOn T (fun T ih hT hp hnf hprod => ?_) hT hp hnf hprod
  have hstep : ∀ k : ℕ, ∀ a ∈ T, (σ^[k]) a ∈ T := by
    intro k
    induction k with
    | zero => intro a ha; simpa using ha
    | succ n ihh => intro a ha; rw [Function.iterate_succ_apply']; exact hT _ (ihh a ha)
  rcases T.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simp
  · set O : Finset α := (Finset.range p).image (fun k => (σ^[k]) a₀) with hOdef
    have hsubeq : ∀ k a, k < p → a = (σ^[k]) a₀ → a ∈ T := by
      intro k a hk ha; subst ha; exact hstep k a₀ ha₀
    have hOsub : O ⊆ T := by
      intro a ha
      rw [hOdef, Finset.mem_image] at ha
      obtain ⟨k, hk, hkO⟩ := ha
      exact hsubeq k a (Finset.mem_range.mp hk) hkO.symm
    have hinj : Set.InjOn (fun k => (σ^[k]) a₀) (Finset.range p) := by
      intro i hi j hj hij
      simp only [Finset.mem_coe, Finset.mem_range] at hi hj
      simp only [] at hij
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have hd : 0 < j - i := by omega
        have hdp : j - i < p := by omega
        have hcast1 : (σ^[j - i]) ((σ^[i]) a₀) = (σ^[j]) a₀ := by
          rw [← Function.iterate_add_apply]; congr 1; omega
        exact hnf ((σ^[j]) a₀) (hstep j a₀ ha₀) (j - i) hd hdp (hij ▸ hcast1)
      · have hd : 0 < i - j := by omega
        have hdp : i - j < p := by omega
        have hcast1 : (σ^[i - j]) ((σ^[j]) a₀) = (σ^[i]) a₀ := by
          rw [← Function.iterate_add_apply]; congr 1; omega
        exact hnf ((σ^[j]) a₀) (hstep j a₀ ha₀) (i - j) hd hdp (hcast1.trans hij)

    have hinjσ : ∀ x ∈ T, ∀ y ∈ T, σ x = σ y → x = y := by
      intro x hx y hy hxy
      have h : (σ^[p-1]) (σ x) = (σ^[p-1]) (σ y) := congrArg _ hxy
      have hx' : (σ^[p-1]) (σ x) = x :=
        (Function.iterate_succ_apply σ (p-1) x).symm.trans
          (by rw [show (p-1).succ = p by omega]; exact hp x hx)
      have hy' : (σ^[p-1]) (σ y) = y :=
        (Function.iterate_succ_apply σ (p-1) y).symm.trans
          (by rw [show (p-1).succ = p by omega]; exact hp y hy)
      exact hx'.symm.trans (h.trans hy')
    have hOcard : O.card = p := by
      rw [hOdef, Finset.card_image_of_injOn hinj, Finset.card_range]
    have hOprod : ∏ a ∈ O, g a = 1 := by
      rw [hOdef, Finset.prod_image hinj]
      exact hprod a₀ ha₀
    have ha₀O : a₀ ∈ O := by
      rw [hOdef, Finset.mem_image]
      exact ⟨0, Finset.mem_range.mpr (Fact.out : p.Prime).pos, by simp⟩
    have hssub : T \ O ⊂ T := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
      intro hcontra
      have : a₀ ∈ T \ O := by rw [hcontra]; exact ha₀
      exact (Finset.mem_sdiff.mp this).2 ha₀O
    have hpσa₀ : σ ((σ^[p-1]) a₀) = a₀ :=
      (Function.iterate_succ_apply' σ (p-1) a₀).symm.trans
        (by rw [show (p-1).succ = p by omega]; exact hp a₀ ha₀)
    have hpred : ∀ b ∈ T \ O, σ b ∈ T \ O := by
      intro b hb
      rw [Finset.mem_sdiff] at hb ⊢
      refine ⟨hT b hb.1, ?_⟩
      intro hbO
      rw [hOdef, Finset.mem_image] at hbO
      obtain ⟨k, hk, hkO⟩ := hbO
      rw [Finset.mem_range] at hk
      have hbO' : b ∈ O := by
        rw [hOdef, Finset.mem_image]
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0
          simp only [Function.iterate_zero_apply] at hkO
          have hb2 : b = (σ^[p-1]) a₀ :=
            hinjσ b hb.1 ((σ^[p-1]) a₀) (hstep (p-1) a₀ ha₀) (by rw [hpσa₀]; exact hkO.symm)
          rw [hb2]
          exact ⟨p-1, Finset.mem_range.mpr (Nat.sub_one_lt (Fact.out : p.Prime).ne_zero), rfl⟩
        · have hb2 : b = (σ^[k-1]) a₀ := by
            apply hinjσ b hb.1 _ (hstep (k-1) a₀ ha₀)
            have hh : σ ((σ^[k-1]) a₀) = (σ^[k]) a₀ := by
              rw [← Function.iterate_succ_apply' σ (k-1) a₀, show (k-1).succ = k by omega]
            rw [hh, hkO]
          rw [hb2]
          exact ⟨k-1, Finset.mem_range.mpr (by omega), rfl⟩
      exact hb.2 hbO'
    have hph : ∀ b ∈ T \ O, (σ^[p]) b = b := fun b hb => hp b (Finset.mem_sdiff.mp hb).1
    have hnfh : ∀ b ∈ T \ O, ∀ k, 0 < k → k < p → (σ^[k]) b ≠ b :=
      fun b hb => hnf b (Finset.mem_sdiff.mp hb).1
    have hprodh : ∀ b ∈ T \ O, ∏ k ∈ Finset.range p, g ((σ^[k]) b) = 1 :=
      fun b hb => hprod b (Finset.mem_sdiff.mp hb).1
    have hIH := ih (T \ O) hssub hpred hph hnfh hprodh
    have hsd := Finset.prod_sdiff hOsub (f := g)
    rw [← hsd, hOprod, hIH, mul_one]


lemma theta_conj_H {G : Type*} [Group G] {H : Subgroup G} {A : Type*} [CommGroup A]
    (θ : H →* A) {y x : G} (hy : y ∈ H) (hx : x ∈ H) (hmem : x⁻¹ * y * x ∈ H) :
    θ ⟨x⁻¹ * y * x, hmem⟩ = θ ⟨y, hy⟩ := by
  have hcoe : (⟨x⁻¹ * y * x, hmem⟩ : H) = ⟨x, hx⟩⁻¹ * ⟨y, hy⟩ * ⟨x, hx⟩ := by
    apply Subtype.ext; simp
  rw [hcoe, map_mul, map_mul, map_inv]
  simp [mul_comm]

lemma smul_one_eq {G : Type*} [Group G] (H : Subgroup G) {uG : G} (hu : uG ∈ H) :
    uG • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
  rw [show uG • ((1 : G) : G ⧸ H) = ((uG * 1 : G) : G ⧸ H) by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]]
  rw [QuotientGroup.eq]
  simpa using hu


lemma cosetKernel_fixes_orbit {G : Type*} [Group G] {H P : Subgroup G} {x : G} {c : G}
    (hc : c ∈ cosetKernel H P x) {γ : G ⧸ H}
    (hγ : γ ∈ MulAction.orbit P ((x : G) : G ⧸ H)) : c • γ = γ := by
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hγ
  rw [← hg]
  change c • ((↑g : G) • ((x : G) : G ⧸ H)) = (↑g : G) • ((x : G) : G ⧸ H)
  rw [show (↑g : G) • ((x : G) : G ⧸ H) = ((↑g * x : G) : G ⧸ H) by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul]]
  exact smul_eq_of_mem_cosetKernel hc g.2

lemma smul_z_smul_comm {G : Type*} [Group G] {H P : Subgroup G} {x z w : G}
    (hw : w ∈ P) (hzP : z ∈ P) (hzcomm : ∀ v ∈ P, ⁅v,z⁆ ∈ cosetKernel H P x) {γ : G ⧸ H}
    (hγ : γ ∈ MulAction.orbit P ((x : G) : G ⧸ H)) : w • (z • γ) = z • (w • γ) := by
  have h1 : w * z = ⁅w,z⁆ * z * w := by rw [commutatorElement_def]; group
  have hwγ : w • γ ∈ MulAction.orbit P ((x : G) : G ⧸ H) := by
    have h := MulAction.mem_orbit γ (⟨w, hw⟩ : ↥P)
    rwa [MulAction.orbit_eq_iff.mpr hγ] at h
  have hzwγ : z • (w • γ) ∈ MulAction.orbit P ((x : G) : G ⧸ H) := by
    have h := MulAction.mem_orbit (w • γ) (⟨z, hzP⟩ : ↥P)
    rwa [MulAction.orbit_eq_iff.mpr hwγ] at h
  calc w • (z • γ) = (w * z) • γ := (mul_smul w z γ).symm
    _ = (⁅w,z⁆ * z * w) • γ := by rw [h1]
    _ = ⁅w,z⁆ • (z • (w • γ)) := by simp only [mul_smul]
    _ = z • (w • γ) := cosetKernel_fixes_orbit (hzcomm w hw) hzwγ



lemma z_no_fixed {G : Type*} [Group G] {H P : Subgroup G} {x z : G}
    (hzP : z ∈ P) (hzK : z ∉ cosetKernel H P x)
    (hzcomm : ∀ v ∈ P, ⁅v,z⁆ ∈ cosetKernel H P x) {γ : G ⧸ H}
    (hγ : γ ∈ MulAction.orbit P ((x : G) : G ⧸ H)) : z • γ ≠ γ := by
  intro hfix
  apply hzK
  rw [mem_cosetKernel_iff_smul]
  refine ⟨hzP, fun y hy => ?_⟩
  obtain ⟨g₁, hg₁⟩ := MulAction.mem_orbit_iff.mp hγ
  have hg₁' : (↑g₁ : G) • ((x : G) : G ⧸ H) = γ := hg₁
  have hyx : y • ((x : G) : G ⧸ H) = (y * (↑g₁)⁻¹) • γ := by
    rw [← hg₁', ← mul_smul]; congr 1; group
  rw [show ((y * x : G) : G ⧸ H) = y • ((x : G) : G ⧸ H) by
      rw [MulAction.Quotient.smul_mk, smul_eq_mul]]
  rw [hyx, ← smul_z_smul_comm (P.mul_mem hy (P.inv_mem g₁.2)) hzP hzcomm hγ, hfix]

lemma zk_ne_self {G : Type*} [Group G] {H P : Subgroup G} {p : ℕ} [Fact p.Prime] {x z : G}
    (hzP : z ∈ P) (hzK : z ∉ cosetKernel H P x) (hzKp : z ^ p ∈ cosetKernel H P x)
    (hzcomm : ∀ v ∈ P, ⁅v,z⁆ ∈ cosetKernel H P x) {γ : G ⧸ H}
    (hγ : γ ∈ MulAction.orbit P ((x : G) : G ⧸ H)) :
    ∀ k, 0 < k → k < p → z ^ k • γ ≠ γ := by
  intro k hk0 hkp hfix
  have hfixp : z ^ p • γ = γ := cosetKernel_fixes_orbit hzKp hγ
  have hdiv : MulAction.period z γ ∣ p := MulAction.pow_smul_eq_iff_period_dvd.mp hfixp
  have hne1 : MulAction.period z γ ≠ 1 := fun h =>
    z_no_fixed hzP hzK hzcomm hγ (MulAction.period_eq_one_iff.mp h)
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdiv with h1 | hp
  · exact hne1 h1
  · exact MulAction.pow_smul_ne_of_lt_period hk0 (by rw [hp]; exact hkp) hfix

lemma smul_z_smul_of_smul_eq {G : Type*} [Group G] {H P : Subgroup G} {x z w : G}
    (hw : w ∈ P) (hzP : z ∈ P) (hzcomm : ∀ v ∈ P, ⁅v,z⁆ ∈ cosetKernel H P x)
    {γ : G ⧸ H} (hγ : γ ∈ MulAction.orbit P ((x : G) : G ⧸ H)) (hfix : w • γ = γ) :
    w • (z • γ) = z • γ := by
  rw [smul_z_smul_comm hw hzP hzcomm hγ, hfix]



lemma orbit_H_prod {G : Type*} [Group G] [Fintype G] {H : Subgroup G} [Fintype (G ⧸ H)]
    {P : Subgroup G} (hPH : P ≤ H) {A : Type*} [CommGroup A] (θ : H →* A)
    (uG : G) (huH : uG ∈ H) :
    (∏ i ∈ Finset.univ.filter (fun i : fixedCosets H uG =>
        Quotient.mk (MulAction.orbitRel P (G ⧸ H)) i.1
          = Quotient.mk (MulAction.orbitRel P (G ⧸ H)) ((1 : G) : G ⧸ H)),
      θ (diagFactor H uG i)) = θ ⟨uG, huH⟩ := by
  classical
  have hmem_orbit : ∀ δ ∈ MulAction.orbit P ((1 : G) : G ⧸ H), δ = ((1 : G) : G ⧸ H) := by
    intro δ hδ
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hδ
    rw [← hg]
    exact smul_one_eq H (hPH g.2)
  have hx : (Quotient.out (((1 : G) : G ⧸ H)) : G) ∈ H := by
    have h := Quotient.out_eq' (((1 : G) : G ⧸ H) : G ⧸ H)
    rw [QuotientGroup.eq] at h
    simpa using H.inv_mem h
  have hfix1 : uG • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := smul_one_eq H huH
  have hfilter : (Finset.univ.filter (fun i : fixedCosets H uG =>
        Quotient.mk (MulAction.orbitRel P (G ⧸ H)) i.1
          = Quotient.mk (MulAction.orbitRel P (G ⧸ H)) ((1 : G) : G ⧸ H)))
      = {(⟨((1 : G) : G ⧸ H), mem_fixedCosets.mpr hfix1⟩ : fixedCosets H uG)} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hi
      apply Subtype.ext
      apply hmem_orbit
      rw [← MulAction.orbitRel_apply, ← Quotient.eq]
      exact hi
    · intro hi; rw [hi]
  rw [hfilter, Finset.prod_singleton]
  exact theta_conj_H θ huH hx (diagFactor H uG ⟨_, mem_fixedCosets.mpr hfix1⟩).2



lemma smul_zpow_smul {G : Type*} [Group G] {H P : Subgroup G} {x z w : G}
    (hw : w ∈ P) (hzP : z ∈ P) (hzcomm : ∀ v ∈ P, ⁅v,z⁆ ∈ cosetKernel H P x)
    {γ : G ⧸ H} (hγ : γ ∈ MulAction.orbit P ((x : G) : G ⧸ H)) (k : ℕ) :
    w • (z ^ k • γ) = z ^ k • (w • γ) := by
  induction k with
  | zero => simp
  | succ n ih =>
      have hγn : z ^ n • γ ∈ MulAction.orbit P ((x : G) : G ⧸ H) := by
        clear ih
        induction n with
        | zero => simpa using hγ
        | succ m ihm =>
            rw [pow_succ', mul_smul]
            have h := MulAction.mem_orbit (z ^ m • γ) (⟨z, hzP⟩ : ↥P)
            rwa [MulAction.orbit_eq_iff.mpr ihm] at h
      rw [pow_succ', mul_smul, smul_z_smul_comm hw hzP hzcomm hγn, ih, mul_smul]



lemma fiber_ne_one_prod {G : Type*} [Group G] [Fintype G] {H : Subgroup G}
    [Fintype (G ⧸ H)] {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    (hPH : (P : Subgroup G) ≤ H) (hz : HallHyp p (P : Subgroup G) H)
    {A : Type*} [CommGroup A] (θ : H →* A) (hexp : ∀ a : A, a ^ p = 1)
    (uG : G) (huH : uG ∈ H) (huP : uG ∈ (P : Subgroup G))
    (j : Quotient (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)))
    (hj : j ≠ Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) ((1 : G) : G ⧸ H)) :
    (∏ i ∈ Finset.univ.filter (fun i : fixedCosets H uG =>
        Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) i.1 = j),
      θ (diagFactor H uG i)) = 1 := by
  classical
  set γ0 : G ⧸ H := j.out with hγ0def
  set x : G := γ0.out with hxdef
  have hxcos : ((x : G) : G ⧸ H) = γ0 := Quotient.out_eq' γ0
  have hxH : x ∉ H := by
    intro h
    apply hj
    have hγ0eq : γ0 = ((1 : G) : G ⧸ H) := by
      rw [← hxcos, QuotientGroup.eq]
      simpa using h
    rw [show j = Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) γ0 from
      (Quotient.out_eq' j).symm, hγ0eq]
  obtain ⟨z, hzP, hzK, hzKp, hzcomm, hzit⟩ := hz x hxH
  have hmemT : ∀ i : fixedCosets H uG,
      Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) i.1 = j →
      i.1 ∈ MulAction.orbit (P : Subgroup G) ((x : G) : G ⧸ H) := by
    intro i hi
    have h1 : Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) i.1
        = Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) ((x : G) : G ⧸ H) := by
      rw [hi]
      exact (Quotient.out_eq' j).symm.trans (congrArg (Quotient.mk _) hxcos).symm
    exact MulAction.orbitRel_apply.mp (Quotient.eq.mp h1)
  have hfix_iter : ∀ (i : fixedCosets H uG)
      (h : Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) i.1 = j) (k : ℕ),
      uG • (z ^ k • i.1) = z ^ k • i.1 := by
    intro i h k
    rw [smul_zpow_smul huP hzP hzcomm (hmemT i h) k, mem_fixedCosets.mp i.2]
  have hiter_mem : ∀ (i : fixedCosets H uG)
      (h : Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) i.1 = j) (k : ℕ),
      Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) (z ^ k • i.1) = j := by
    intro i h k
    have hq : Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) (z ^ k • i.1)
        = Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) i.1 :=
      Quotient.sound (MulAction.orbitRel_apply.mpr
        (MulAction.mem_orbit i.1 (⟨z ^ k, (P : Subgroup G).pow_mem hzP k⟩ : ↥(P : Subgroup G))))
    rw [hq, h]
  let σ : fixedCosets H uG → fixedCosets H uG := fun i =>
    if h : Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) i.1 = j
    then ⟨z • i.1, mem_fixedCosets.mpr
      (smul_z_smul_of_smul_eq huP hzP hzcomm (hmemT i h) (mem_fixedCosets.mp i.2))⟩
    else i
  have hσ_apply : ∀ (i : fixedCosets H uG)
      (h : Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) i.1 = j),
      σ i = ⟨z • i.1, mem_fixedCosets.mpr (by simpa [pow_one] using hfix_iter i h 1)⟩ := by
    intro i h
    simp only [σ, dif_pos h]
  have σ_iter : ∀ (i : fixedCosets H uG)
      (h : Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) i.1 = j) (k : ℕ),
      (σ^[k]) i = ⟨z ^ k • i.1, mem_fixedCosets.mpr (hfix_iter i h k)⟩ := by
    intro i h k
    induction k with
    | zero =>
        simp only [Function.iterate_zero_apply]
        apply Subtype.ext; simp
    | succ n ih =>
        have h1 : (σ^[n+1]) i = σ ((σ^[n]) i) := Function.iterate_succ_apply' σ n i
        rw [h1]
        have h2 : (σ^[n]) i = ⟨z ^ n • i.1, mem_fixedCosets.mpr (hfix_iter i h n)⟩ := ih
        rw [h2]
        simp only [σ, dif_pos (hiter_mem i h n)]
        apply Subtype.ext
        change z • (z ^ n • i.1) = z ^ (n + 1) • i.1
        rw [pow_succ', mul_smul]
  have hT : ∀ i ∈ Finset.univ.filter (fun i : fixedCosets H uG =>
        Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) i.1 = j),
      σ i ∈ Finset.univ.filter (fun i : fixedCosets H uG =>
        Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) i.1 = j) := by
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hσ_apply i hi.2]
    simpa [pow_one] using hiter_mem i hi.2 1
  have hpσ : ∀ i ∈ Finset.univ.filter (fun i : fixedCosets H uG =>
        Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) i.1 = j),
      (σ^[p]) i = i := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [σ_iter i hi.2 p]
    exact Subtype.ext (cosetKernel_fixes_orbit hzKp (hmemT i hi.2))
  have hnfσ : ∀ i ∈ Finset.univ.filter (fun i : fixedCosets H uG =>
        Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) i.1 = j),
      ∀ k, 0 < k → k < p → (σ^[k]) i ≠ i := by
    intro i hi k hk0 hkp hcontra
    rw [Finset.mem_filter] at hi
    have hval : z ^ k • i.1 = i.1 := by
      have hthis := congrArg Subtype.val hcontra
      rw [σ_iter i hi.2 k] at hthis
      exact hthis
    exact zk_ne_self hzP hzK hzKp hzcomm (hmemT i hi.2) k hk0 hkp hval
  have hprodσ : ∀ i ∈ Finset.univ.filter (fun i : fixedCosets H uG =>
        Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) i.1 = j),
      ∏ k ∈ Finset.range p, θ (diagFactor H uG ((σ^[k]) i)) = 1 := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have hfun : ∀ k ∈ Finset.range p, θ (diagFactor H uG ((σ^[k]) i))
        = θ (diagFactor H uG ⟨z ^ k • i.1, mem_fixedCosets.mpr (hfix_iter i hi.2 k)⟩) := by
      intro k _
      rw [σ_iter i hi.2 k]
    rw [Finset.prod_congr rfl hfun]
    exact cycle_prod_eq_one θ hexp (hzit uG huP) i.1 (hfix_iter i hi.2)
  exact free_prod_eq_one σ (fun i => θ (diagFactor H uG i))
    (Finset.univ.filter (fun i : fixedCosets H uG =>
      Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) i.1 = j))
    hT hpσ hnfσ hprodσ



theorem prod_diagFactor_eq {G : Type*} [Group G] [Fintype G] {H : Subgroup G} [Fintype (G ⧸ H)]
    {p : ℕ} [Fact p.Prime] {P : Sylow p G} (hPH : (P : Subgroup G) ≤ H)
    (hz : Work.Grun.HallHyp p (P : Subgroup G) H)
    {A : Type*} [CommGroup A] (θ : H →* A) (hexp : ∀ a : A, a ^ p = 1) (u : (P : Subgroup G)) :
    Work.Grun.diagProd θ (u : G) = θ ⟨(u : G), hPH u.2⟩ := by
  classical
  have huH : (u : G) ∈ H := hPH u.2
  have hfiber := Finset.prod_fiberwise (Finset.univ : Finset (fixedCosets H (u : G)))
      (fun i : fixedCosets H (u : G) =>
        Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) i.1)
      (fun i => θ (diagFactor H (u : G) i))
  rw [diagProd_def, ← hfiber]
  set j0 : Quotient (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) :=
    Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) ((1 : G) : G ⧸ H) with hj0def
  rw [← Finset.mul_prod_erase (Finset.univ)
      (fun j => ∏ i ∈ Finset.univ.filter (fun i : fixedCosets H (u : G) =>
        Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) i.1 = j),
        θ (diagFactor H (u : G) i)) (Finset.mem_univ j0)]
  rw [hj0def]
  have h1 : (∏ i ∈ Finset.univ.filter (fun i : fixedCosets H (u : G) =>
        Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) i.1
          = Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) ((1 : G) : G ⧸ H)),
        θ (diagFactor H (u : G) i)) = θ ⟨(u : G), huH⟩ :=
    orbit_H_prod hPH θ (u : G) huH
  have h2 : (∏ j ∈ (Finset.univ : Finset (Quotient (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)))).erase
        (Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) ((1 : G) : G ⧸ H)),
      ∏ i ∈ Finset.univ.filter (fun i : fixedCosets H (u : G) =>
        Quotient.mk (MulAction.orbitRel (P : Subgroup G) (G ⧸ H)) i.1 = j),
        θ (diagFactor H (u : G) i)) = 1 := by
    refine Finset.prod_eq_one (fun j hj => ?_)
    rw [Finset.mem_erase] at hj
    exact fiber_ne_one_prod hPH hz θ hexp (u : G) huH u.2 j hj.1
  rw [h1, h2, mul_one]


end Work.Grun
