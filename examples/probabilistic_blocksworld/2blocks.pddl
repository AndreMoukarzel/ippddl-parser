(define (problem 2blocks)
  (:domain blocks-domain)
  (:objects b1 b2 - block)
  (:init (emptyhand) (on-table b1) (on-table b2) (clear b1) (clear b2))
  (:goal (and (emptyhand) (on b1 b2) (on-table b2) (clear b1)))
  (:goal-reward 1)
  (:metric maximize (reward))
)