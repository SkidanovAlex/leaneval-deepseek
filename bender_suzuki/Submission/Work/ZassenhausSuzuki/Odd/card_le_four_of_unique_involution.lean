import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ZassenhausSuzuki.Odd

/-- In a finite group of exponent dividing `4` with a unique involution, in which no element is
conjugated to its inverse unless it is an involution, and whose commutators are involutions,
every element has order at most `4`.  (The hypothesis `hccent` that commutators are central is
not needed.) -/
theorem card_le_four_of_unique_involution {R : Type} [Group R] [Finite R]
    (hexp : ∀ x : R, x ^ 4 = 1)
    (huniq : ∀ u v : R, u * u = 1 → v * v = 1 → u ≠ 1 → v ≠ 1 → u = v)
    (hnoinv : ∀ x y : R, y * x * y⁻¹ = x⁻¹ → x * x = 1)
    (hcsq : ∀ a b : R, (a * b * a⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹) = 1)
    (hccent : ∀ a b c : R, c * (a * b * a⁻¹ * b⁻¹) = (a * b * a⁻¹ * b⁻¹) * c) :
    Nat.card R ≤ 4 := by
  classical
  -- Every square is an involution.
  have hA : ∀ x : R, (x*x)*(x*x) = 1 := by
    intro x
    have h : (x*x)*(x*x) = x^4 := by rw [← pow_two x, ← pow_add]
    rw [h]; exact hexp x
  -- The group is abelian.
  have hab : ∀ x y : R, x * y = y * x := by
    by_cases hexp2 : ∀ t : R, t * t = 1
    · -- exponent 2: the group is abelian
      intro x y
      have hxy : (x*y)*(x*y) = 1 := hexp2 (x*y)
      have hxy' : x*y = (x*y)⁻¹ := eq_inv_of_mul_eq_one_left hxy
      have hx : x⁻¹ = x := (eq_inv_of_mul_eq_one_left (hexp2 x)).symm
      have hy : y⁻¹ = y := (eq_inv_of_mul_eq_one_left (hexp2 y)).symm
      rw [hxy', mul_inv_rev, hx, hy]
    · obtain ⟨x0, hx0⟩ := not_forall.mp hexp2
      have hzz : (x0*x0)*(x0*x0) = 1 := hA x0
      have hz1 : x0*x0 ≠ 1 := hx0
      have huniqz : ∀ v : R, v*v = 1 → v ≠ 1 → v = x0*x0 :=
        fun v hv hv1 => huniq v (x0*x0) hv hzz hv1 hz1
      -- Every element of order 4 is central.
      have hcen4 : ∀ w : R, w*w ≠ 1 → ∀ y : R, y*w = w*y := by
        intro w hw y
        have hcc : (y*w*y⁻¹*w⁻¹) * (y*w*y⁻¹*w⁻¹) = 1 := hcsq y w
        by_cases hc1 : y*w*y⁻¹*w⁻¹ = 1
        · have hyw : y*w*y⁻¹ = w := by
            have h := congrArg (fun t => t * w) hc1
            rw [one_mul] at h
            rwa [show (y*w*y⁻¹*w⁻¹)*w = y*w*y⁻¹ by group] at h
          calc y*w = y*w*y⁻¹*y := by group
            _ = w*y := by rw [hyw]
        · have hcz : y*w*y⁻¹*w⁻¹ = x0*x0 := huniqz _ hcc hc1
          have hzww : x0*x0 = w*w := (huniqz (w*w) (hA w) hw).symm
          have hywinv : y*w*y⁻¹ = w⁻¹ := by
            calc y*w*y⁻¹ = (y*w*y⁻¹*w⁻¹)*w := by group
              _ = (x0*x0)*w := by rw [hcz]
              _ = (w*w)*w := by rw [hzww]
              _ = w⁻¹ := by
                rw [show (w*w)*w = w^3 by rw [← pow_two w]; exact (pow_succ w 2).symm]
                apply eq_inv_of_mul_eq_one_left
                rw [show w^3 * w = w^4 from (pow_succ w 3).symm, hexp w]
          exact absurd (hnoinv w y hywinv) hw
      intro x y
      by_cases hx : x*x = 1
      · by_cases hx1 : x = 1
        · rw [hx1]; simp
        · -- `x` is the unique involution `x0*x0`
          have hxz : x = x0*x0 := huniqz x hx hx1
          have hx0cen : ∀ t : R, t*x0 = x0*t := hcen4 x0 hx0
          have hzcen : ∀ t : R, t*(x0*x0) = (x0*x0)*t := by
            intro t
            calc t*(x0*x0) = (t*x0)*x0 := by group
              _ = (x0*t)*x0 := by rw [hx0cen t]
              _ = x0*(t*x0) := by group
              _ = x0*(x0*t) := by rw [hx0cen t]
              _ = (x0*x0)*t := by group
          rw [hxz]
          exact (hzcen y).symm
      · exact (hcen4 x hx y).symm
  letI : CommGroup R := { ‹Group R› with mul_comm := hab }
  -- the squaring homomorphism
  let f : R →* R := MonoidHom.mk' (fun x => x^2) (fun a b => mul_pow a b 2)
  have hcard : Nat.card R = Nat.card ↥f.range * Nat.card ↥f.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  -- any subgroup all of whose elements square to `1` has at most two elements
  have hbound : ∀ (K : Subgroup R), (∀ x ∈ K, x * x = 1) → Nat.card ↥K ≤ 2 := by
    intro K hK
    have hinj : Function.Injective
        (fun x : ↥K => if (x : R) = 1 then (0 : Fin 2) else 1) := by
      intro x y hxy
      dsimp only at hxy
      have hx2 : (x : R) * (x : R) = 1 := hK x x.2
      have hy2 : (y : R) * (y : R) = 1 := hK y y.2
      by_cases hx1 : (x : R) = 1
      · have hy1 : (y : R) = 1 := by
          by_contra hy1
          have hx0 : (if (x:R) = 1 then (0:Fin 2) else 1) = 0 := by rw [ite_eq_left hx1]
          have hy0 : (if (y:R) = 1 then (0:Fin 2) else 1) = 1 := by rw [ite_eq_right hy1]
          rw [hx0, hy0] at hxy
          exact absurd hxy (by decide)
        exact Subtype.ext (by rw [hx1, hy1])
      · have hy1 : (y : R) ≠ 1 := by
          intro hy1
          have hx0 : (if (x:R) = 1 then (0:Fin 2) else 1) = 1 := by rw [ite_eq_right hx1]
          have hy0 : (if (y:R) = 1 then (0:Fin 2) else 1) = 0 := by rw [ite_eq_left hy1]
          rw [hx0, hy0] at hxy
          exact absurd hxy.symm (by decide)
        exact Subtype.ext (huniq _ _ hx2 hy2 hx1 hy1)
    have := Nat.card_le_card_of_injective _ hinj
    simpa [Nat.card_eq_fintype_card, Fintype.card_fin] using this
  have hker2 : Nat.card ↥f.ker ≤ 2 := hbound f.ker (fun x hx => by
    have h : (x : R)^2 = 1 := MonoidHom.mem_ker.mp hx
    rwa [pow_two] at h)
  have hrange2 : Nat.card ↥f.range ≤ 2 := hbound f.range (fun x hx => by
    rw [MonoidHom.mem_range] at hx
    obtain ⟨y, hy⟩ := hx
    have hy' : y^2 = x := hy
    rw [← hy']
    rw [show y^2 * y^2 = y^4 by rw [← pow_add], hexp y])
  calc Nat.card R = Nat.card ↥f.range * Nat.card ↥f.ker := hcard
    _ ≤ 2 * 2 := Nat.mul_le_mul hrange2 hker2
    _ = 4 := by norm_num

end Work.ZassenhausSuzuki.Odd
