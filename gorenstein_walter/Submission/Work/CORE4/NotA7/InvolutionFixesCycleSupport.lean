import Mathlib

namespace Work.CORE4.NotA7

/-- An involution of `A₇` that centralizes a cycle `x` fixes every point in the support of `x`.

The argument is that a permutation commuting with a cycle `x` permutes the (single) cycle
`x.support` and acts on it as a power `x ^ i` of `x`; since the involution `y` satisfies
`y ^ 2 = 1` this forces `x ^ (2 * i) = 1`, hence `orderOf x ∣ 2 * i`. As `x ∈ A₇` is a cycle
its sign is `1`, so `orderOf x` is odd, giving `orderOf x ∣ i` and therefore `y` acts as
`x ^ i = 1` on the support of `x`. -/
theorem InvolutionFixesCycleSupport {x y : alternatingGroup (Fin 7)}
    (hx : (x : Equiv.Perm (Fin 7)).IsCycle)
    (hy : y ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 7))))
    (hy2 : orderOf y = 2) :
    ∀ a ∈ (x : Equiv.Perm (Fin 7)).support, (y : Equiv.Perm (Fin 7)) a = a := by
  set X : Equiv.Perm (Fin 7) := (x : Equiv.Perm (Fin 7)) with hX
  set Y : Equiv.Perm (Fin 7) := (y : Equiv.Perm (Fin 7)) with hY
  have hx' : X.IsCycle := hx
  -- `y` commutes with `x`, hence `Y` commutes with `X`.
  have hcomm_group : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp hy
  have hcomm : Y * X = X * Y := by
    have h := congrArg (fun z : alternatingGroup (Fin 7) => (z : Equiv.Perm (Fin 7))) hcomm_group
    simpa [hX, hY] using h
  -- `y` is an involution, hence `Y ^ 2 = 1`.
  have hY2 : Y ^ 2 = 1 := by
    have h : y ^ 2 = 1 := by rw [← hy2]; exact pow_orderOf_eq_one y
    have hh := congrArg (fun z : alternatingGroup (Fin 7) => (z : Equiv.Perm (Fin 7))) h
    simpa [hX, hY] using hh
  -- `x ∈ A₇` has sign `1`.
  have hsign : Equiv.Perm.sign X = 1 := by
    have := Equiv.Perm.mem_alternatingGroup.mp x.2
    simpa [hX] using this
  -- A cycle with sign `1` has odd order.
  have hodd : Odd (orderOf X) := by
    have hk : Equiv.Perm.sign X = -(-1 : ℤˣ) ^ X.support.card := Equiv.Perm.IsCycle.sign hx'
    rw [hsign] at hk
    have h2 : (-1 : ℤˣ) ^ X.support.card = -1 := by
      have := congrArg Neg.neg hk
      simpa using this.symm
    have ho : Odd X.support.card := by
      rw [← neg_one_pow_eq_neg_one_iff_odd (by decide : (-1 : ℤˣ) ≠ 1)]
      exact h2
    rwa [Equiv.Perm.IsCycle.orderOf hx']
  intro a ha
  rw [Equiv.Perm.mem_support] at ha
  -- `Y` maps the support of `X` to itself.
  have hYX : ∀ b, X (Y b) = Y (X b) := fun b => by
    have := DFunLike.congr_fun hcomm b
    simpa [Equiv.Perm.mul_apply] using this.symm
  have hYa_ne : X (Y a) ≠ Y a := by
    rw [hYX]
    intro h
    exact ha (Y.injective h)
  -- Since `X` is a cycle, `Y a` is a power of `X` applied to `a`.
  obtain ⟨i, hi⟩ := Equiv.Perm.IsCycle.exists_pow_eq hx' ha hYa_ne
  have hYcomm : Commute Y X := hcomm
  have hYXi : Y * X ^ i = X ^ i * Y := (hYcomm.pow_right i).eq
  -- Applying `y` twice returns `a`, so `X ^ (2 * i)` fixes `a`.
  have key : (X ^ (2 * i)) a = a := by
    calc (X ^ (2 * i)) a = (X ^ i) ((X ^ i) a) := by
            rw [two_mul, pow_add, Equiv.Perm.mul_apply]
      _ = (X ^ i) (Y a) := by rw [hi]
      _ = (X ^ i * Y) a := by rw [Equiv.Perm.mul_apply]
      _ = (Y * X ^ i) a := by rw [hYXi]
      _ = Y ((X ^ i) a) := by rw [Equiv.Perm.mul_apply]
      _ = Y (Y a) := by rw [hi]
      _ = (Y * Y) a := by rw [Equiv.Perm.mul_apply]
      _ = (Y ^ 2) a := by rw [sq]
      _ = a := by rw [hY2]; rfl
  have hpow : X ^ (2 * i) = 1 := (Equiv.Perm.IsCycle.pow_eq_one_iff' hx' ha).mpr key
  have hdvd : orderOf X ∣ 2 * i := orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hcop : (orderOf X).Coprime 2 := Nat.coprime_two_right.mpr hodd
  have hdvd' : orderOf X ∣ i := hcop.dvd_of_dvd_mul_left hdvd
  have hXi : X ^ i = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd'
  rw [← hi, hXi, Equiv.Perm.one_apply]

end Work.CORE4.NotA7
