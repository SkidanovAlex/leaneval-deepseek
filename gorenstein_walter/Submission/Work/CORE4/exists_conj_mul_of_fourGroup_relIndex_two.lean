import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.cyclic_order_two_unique

namespace Work.CORE4

/-- **A Klein four subgroup of index two captures the `T`-conjugacy class of an involution
outside it.**

Let `T ≤ S` be a subgroup of index two with `T` a Klein four group (`Work.GW2.IsFourGroup T`),
let `y ∈ S \ T` be an involution and `1 ≠ c ∈ T` commute with `y`.  If `S` contains an element
of order `> 2` (so that `S` is not elementary abelian), then `y` does not centralise `T`, and
`c` is the square of an element of the coset `yT`:

  `∃ p ∈ T, p * y * p⁻¹ = y * c`.

Indeed `p * y * p⁻¹ = y * c` is equivalent (as `p² = y² = 1`) to `c = (y p)² = y*p*y*p`,
so the claim is that the map `p ↦ (y p)²` from `T` to `T` hits `c`.

Route.  `T` is normal in `S` (index two) and abelian; write `K = T ⊓ C_X(y)`.  Since `y`
does not centralise `T` (`y` centralising `T` forces `S = T ∪ yT` to be elementary abelian,
contradicting the element of order `> 2`), `K` is a proper subgroup of `T`; also
`c ∈ K \ {1}` and `2 ∣ |K| ∣ |T| = 4`, so `|K| = 2`.  Fix `q ∈ T` with `y*q ≠ q*y`.  Then
`β = y*q*y*q ∈ T` and `y β y = q (y q y) = (y q y) q = β` (the last step by commutativity of
`T` and `hconj`), i.e. `β ∈ K`; and `β ≠ 1` because `β = 1` gives `y q y = q` and hence
`y q = q y`.  As `|K| = 2` and `c, β ∈ K \ {1}` we get `β = c`, i.e. `c = y*q*y*q`; taking
`p = q` (an involution) gives `q y q⁻¹ = y c`. -/
theorem exists_conj_mul_of_fourGroup_relIndex_two {X : Type} [Group X] (T S : Subgroup X) (y c : X)
    (hTS : T ≤ S) (hrel : T.relIndex S = 2) (hT4 : Work.GW2.IsFourGroup T) (hyS : y ∈ S)
    (hyT : y ∉ T) (hy2 : y * y = 1) (hcT : c ∈ T) (hc1 : c ≠ 1) (hcy : c * y = y * c)
    (hne : ∃ x ∈ S, x * x ≠ 1) : ∃ p ∈ T, p * y * p⁻¹ = y * c := by
  classical
  -- ## 0. Elementary consequences of `IsFourGroup T`.
  have hT2 : ∀ v ∈ T, v * v = 1 := fun v hv => by
    have h := hT4.2 v hv
    rwa [pow_two] at h
  have hTcomm : ∀ u ∈ T, ∀ v ∈ T, u * v = v * u := by
    intro u hu v hv
    have huv : (u * v) * (u * v) = 1 := hT2 (u * v) (T.mul_mem hu hv)
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_left (hT2 u hu)
    have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_left (hT2 v hv)
    have h3 : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_left huv
    rw [mul_inv_rev, hu', hv'] at h3
    exact h3.symm
  have hcardT : Nat.card T = 4 := hT4.1
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy2
  -- `y` is an involution, so `y * (y * a) = a`.
  have hyy : ∀ a : X, y * (y * a) = a := fun a => by rw [← mul_assoc, hy2, one_mul]
  -- ## 1. `T` is normal in `S` (index two), so conjugating by `y` stays inside `T`.
  have hTnorm : (T.subgroupOf S).Normal := Subgroup.normal_of_index_eq_two hrel
  have hconj : ∀ t ∈ T, y * t * y⁻¹ ∈ T :=
    (Subgroup.le_normalizer_iff.mp
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hTS).mp hTnorm)) y hyS
  -- ## 2. `y` does not centralise `T`.
  have hy_not_cent : ∃ q ∈ T, y * q ≠ q * y := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨x, hxS, hx2⟩ := hne
    have hxT : x ∉ T := fun hx => hx2 (hT2 x hx)
    -- `x` and `y` lie in the same non-trivial coset of `T` in `S`, so `y * x ∈ T`.
    have hyxT : y * x ∈ T := by
      have h := (Subgroup.mul_mem_iff_of_index_two (H := T.subgroupOf S) hrel
        (a := (⟨y, hyS⟩ : S)) (b := (⟨x, hxS⟩ : S))).mpr (by
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
          exact iff_of_false hyT hxT)
      simpa [Subgroup.mem_subgroupOf] using h
    -- hence `x = y * (y * x)` is the product of `y` with an element of `T`
    have hx_eq : x = y * (y * x) := (hyy x).symm
    have hkey : (y * (y * x)) * (y * (y * x)) = 1 := by
      have hsy : y * (y * x) = (y * x) * y := hcon (y * x) hyxT
      calc (y * (y * x)) * (y * (y * x))
          = ((y * x) * y) * (y * (y * x)) := congrArg (fun w => w * (y * (y * x))) hsy
        _ = (y * x) * (y * (y * (y * x))) := by rw [mul_assoc]
        _ = (y * x) * (y * x) := by rw [hyy (y * x)]
        _ = 1 := hT2 (y * x) hyxT
    have hxx : x * x = 1 := by rw [hx_eq]; exact hkey
    exact hx2 hxx
  obtain ⟨q, hqT, hqnc⟩ := hy_not_cent
  -- ## 3. `K := T ⊓ C_X(y)` has order two and its non-trivial element is `c`.
  set K : Subgroup X := T ⊓ Subgroup.centralizer ({y} : Set X) with hK
  have hKT : K ≤ T := by rw [hK]; exact inf_le_left
  have hcK : c ∈ K := ⟨hcT, Subgroup.mem_centralizer_singleton_iff.mpr hcy⟩
  have hqK : q ∉ K := by
    rintro ⟨-, hqcen⟩
    exact hqnc (Subgroup.mem_centralizer_singleton_iff.mp hqcen).symm
  have hKne : K ≠ T := fun h => hqK (h ▸ hqT)
  have hKdvd : Nat.card K ∣ 4 := by
    have h := Subgroup.relIndex_mul_card K T
    rw [inf_eq_left.mpr hKT, hcardT] at h
    exact ⟨K.relIndex T, by rw [mul_comm]; exact h.symm⟩
  have hKne0 : Nat.card K ≠ 0 := by
    intro h0
    rw [h0] at hKdvd
    exact absurd hKdvd (by norm_num)
  haveI : Finite K := Nat.finite_of_card_ne_zero hKne0
  haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hcardT]; norm_num)
  have hordc : orderOf c = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hT2 c hcT) hc1
  have hKcard : Nat.card K = 2 := by
    have hne4 : Nat.card K ≠ 4 := by
      intro h4
      exact hKne (Subgroup.eq_of_le_of_card_ge hKT (by rw [hcardT, h4]))
    have hge2 : 2 ≤ Nat.card K := by
      have h := Subgroup.card_le_of_le (H := Subgroup.zpowers c) (K := K)
        (Subgroup.zpowers_le.mpr hcK)
      rwa [Nat.card_zpowers, hordc] at h
    obtain ⟨m, hm⟩ := hKdvd
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [h0, mul_zero] at hm
        exact absurd hm (by norm_num)
      · exact hpos
    have hmle : m ≤ 3 := by
      by_contra hlt
      push_neg at hlt
      have hbig : 4 < Nat.card K * m := by
        calc 4 < 2 * 4 := by norm_num
          _ ≤ Nat.card K * m := Nat.mul_le_mul hge2 (by omega)
      omega
    interval_cases m <;> omega
  -- `K = ⟨c⟩`, so its only non-trivial element is `c`.
  have hKzp : K = Subgroup.zpowers c := by
    refine (Subgroup.eq_of_le_of_card_ge (H := Subgroup.zpowers c) (K := K)
      (Subgroup.zpowers_le.mpr hcK) ?_).symm
    rw [Nat.card_zpowers, hordc, hKcard]
  have hKmem : ∀ h ∈ K, h = 1 ∨ h = c := by
    intro h hh
    have hh' : h ∈ Subgroup.zpowers c := hKzp ▸ hh
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hh'
    have hc2z : c ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two]
      exact hT2 c hcT
    rcases zpow_eq_one_or_self_of_sq_eq_one hc2z n with h1 | h1
    · exact Or.inl (hn ▸ h1)
    · exact Or.inr (hn ▸ h1)
  -- ## 4. `β = y*q*y*q` is a non-trivial element of `K`, hence `β = c`.
  have hwT : y * q * y ∈ T := by
    have h := hconj q hqT
    rwa [hyinv] at h
  have hβT : y * q * y * q ∈ T := T.mul_mem hwT hqT
  have h1 : y * (y * q * y * q) = q * y * q := by
    simp only [mul_assoc]
    exact hyy (q * (y * q))
  have h2aux : (y * q * y * q) * y = q * (y * q) := by
    have hstep : (y * q * y * q) * y = (y * q * y) * (q * y) := by group
    rw [hstep]
    have hcw : (y * q * y) * q = q * (y * q * y) := (hTcomm q hqT (y * q * y) hwT).symm
    calc (y * q * y) * (q * y) = ((y * q * y) * q) * y := by group
      _ = (q * (y * q * y)) * y := by rw [hcw]
      _ = q * (y * q) := by
            have hA : (q * (y * q * y)) * y = q * ((y * q * y) * y) := mul_assoc q (y * q * y) y
            have hB : (y * q * y) * y = y * q := by
              simp only [mul_assoc, hy2, mul_one]
            rw [hA, hB]
  have h2 : (y * q * y * q) * y = q * y * q := by
    rw [h2aux]
    exact (mul_assoc q y q).symm
  have hyβ : y * (y * q * y * q) = (y * q * y * q) * y := h1.trans h2.symm
  have hβK : y * q * y * q ∈ K :=
    ⟨hβT, Subgroup.mem_centralizer_singleton_iff.mpr hyβ.symm⟩
  have hβne1 : y * q * y * q ≠ 1 := by
    intro h
    apply hqnc
    have hq2 : q * q = 1 := hT2 q hqT
    have h1' : y * q * y = q := by
      have hh : (((y * q) * y) * q) * q = 1 * q := congrArg (· * q) h
      simpa [mul_assoc, hq2] using hh
    have h2' : y * (y * q * y) = q * y := by
      calc y * (y * q * y) = y * (y * (q * y)) := by rw [← mul_assoc y q y]
        _ = q * y := hyy (q * y)
    have hh := congrArg (fun z => y * z) h1'
    rw [h2'] at hh
    exact hh.symm
  have hcβ : c = y * q * y * q := by
    rcases hKmem (y * q * y * q) hβK with h | h
    · exact absurd h hβne1
    · exact h.symm
  -- ## 5. `p = q` is the required witness.
  refine ⟨q, hqT, ?_⟩
  have hqinv : q⁻¹ = q := inv_eq_of_mul_eq_one_left (hT2 q hqT)
  rw [hqinv, hcβ]
  exact h1.symm

end Work.CORE4
