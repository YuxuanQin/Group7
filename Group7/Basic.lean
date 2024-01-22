import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.Algebra.Lie.Basic


-- set_option autoImplicit false


@[simp]
theorem decompose (k V : Type*) [Field k] [AddCommGroup V] [Module k V] (b : Basis (Fin 1) k V) :
    ∀ (v : V), v = (b.repr v 0) • (b 0) := by
  intro v
  nth_rewrite 1 [← b.total_repr v]
  have hsubset : (b.repr v).support ⊆ {0} := by
    intro x _
    rewrite [Finset.mem_singleton]
    exact Fin.eq_zero x
  have hzero : ∀ x ∈ ({0} : Finset (Fin 1)), x ∉ (b.repr v).support → (b.repr v) x • b x = 0 := by
    intro i hi
    rw [Finset.mem_singleton] at hi
    rw [hi, Finsupp.mem_support_iff.not, not_ne_iff]
    intro hc
    rw [hc]
    exact zero_smul k (b 0)
  rw [Finsupp.total_apply, Finsupp.sum, Finset.sum_subset hsubset hzero,
   Finset.sum_singleton]


variable {U V P Q: Type*}

variable [Field V]
variable [AddCommGroup U]
variable [Module V U] -- U is a vector space on V.


variable [LieRing P] [LieRing Q]
variable [LieAlgebra V P] [LieAlgebra V Q]


-- `variable (m : AddCommMonoid U)` is not a good way.



-- Below we define "the" trivial Lie algebra: its Lie bracket
-- is trivial. Notice that we don't claim about its dimension.

@[simp]
instance trivial_bracket : Bracket U U where
  bracket := fun _ _ => 0

-- Here `@` acts as a "register" to tell lean4 that we can
-- use the tactic `simp` to reduce some experesions involve
-- `trivial_bracket.bracket`.
-- As the following example goes:


@[simp]
instance trivial_LR : LieRing U where
  add_lie := by simp
  lie_add := by simp
  lie_self := by simp
  leibniz_lie := by simp

-- Try not registe `trivial_bracket.bracket`, i.e., delete
-- the `@[simp]` and see what will happend.


@[simp]
instance trivial_LA : LieAlgebra V U where
  lie_smul := by
    simp


theorem one_dim :
  Basis (Fin 1) V U -> Basis (Fin 1) V P
  -> LieEquiv V P U := by
  intro u p
  constructor
  pick_goal 4
  · intro x
    exact ((u.repr x) 0 • (p 0))
  pick_goal 3
  · constructor
    pick_goal 2
    · constructor
      pick_goal 2
      · constructor
        pick_goal 2
        · intro y
          exact ((p.repr y) 0 • (u 0))
        · simp
          intro x y
          rw [add_smul]
      · intro r x
        simp
        simp [DFunLike.coe]
        simp [EquivLike.coe]
        apply u.ext_elem_iff.2
        intro i
        simp
        exact rfl
    · simp
      intro x y
      have nox : x = (p.repr x 0) • (p 0) := by exact decompose V P p x
      have noy : y = (p.repr y 0) • (p 0) := by exact decompose V P p y
      rw [nox, noy]
      simp
  · rw [Function.LeftInverse]
    simp
    intro x
    nth_rewrite 2 [decompose V P p x]
    rfl
  intro x
  simp
  nth_rewrite 2 [decompose V U u x]
  rfl
